#!/usr/bin/env python3
"""post-results: post the xrepo-review check run, the pull request comment, and the job summary.

The review workflow (review.yml) runs this script through the post-results composite action.
It needs only the Python 3 standard library (3.9 or newer) and calls the GitHub REST API with
GITHUB_TOKEN (or GH_TOKEN).

What it posts, by mode (from GET /v1/repo-config) and step (chosen by review.yml):

    shadow, off        the job summary only; nothing on the pull request
    advisory,          step queue: the check run `xrepo-review` with success, no comment
    required, or       step unavailable, or no usable result.json: a neutral check run
    unknown (the         "Review unavailable"; the pull request comment is not changed
    settings could     step review: create the check run first (check_run_id is written at
    not be read)         once), then complete it with the conclusion, title, summary, text,
                         and at most 50 annotations (highest severity first, at most 50 per
                         request), and create or update the one pull request comment that
                         contains <!-- xrepo-review -->. A result with status unavailable
                         only updates an existing comment; it never creates one.

A conclusion of failure is posted only in mode required; any other failure becomes neutral.
GitHub treats neutral as passing, so the reviewer can block a merge only through a required
rule. Requests are retried on 5xx responses, network errors, and rate limits.

Inputs: command-line options, or the environment variables that action.yml sets (see
parse_args). Environment: GITHUB_TOKEN or GH_TOKEN, GITHUB_REPOSITORY, GITHUB_API_URL (defaults
to the GitHub REST API), GITHUB_OUTPUT, GITHUB_STEP_SUMMARY, and GITHUB_SERVER_URL with
GITHUB_RUN_ID for the link to the run. Outputs: check_run_id (as soon as the check run exists),
conclusion (when the check run is complete), comment_id. The exit code is 1 when anything could
not be posted; the review workflow then completes the check run as neutral.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from typing import Any

CHECK_NAME = "xrepo-review"
COMMENT_MARKER = "<!-- xrepo-review -->"
MAX_ANNOTATIONS = 50  # in total, highest severity first
ANNOTATIONS_PER_REQUEST = 50  # GitHub Checks API limit per request (later requests append)
MAX_TITLE = 255
MAX_OUTPUT_TEXT = 65_535  # output.summary and output.text, in characters
MAX_ANNOTATION_MESSAGE_BYTES = 64 * 1024
MAX_COMMENT = 65_000  # below the GitHub comment body limit of 65,536 characters
MAX_PAGES = 100  # 100 comments per page
BACKOFF_SECONDS = (2.0, 4.0, 8.0)  # retries after 5xx responses and network errors
MAX_RATE_LIMIT_WAIT = 90.0  # a rate limit that lasts longer is not waited for
TIMEOUT_SECONDS = 30
SLEEP = time.sleep  # replaced in tests

MODES = ("off", "shadow", "advisory", "required")
STEPS = ("review", "queue", "unavailable")
CONCLUSIONS = ("success", "neutral", "failure")
LEVEL_ORDER = {"failure": 0, "warning": 1, "notice": 2}

UNAVAILABLE_TITLE = "Review unavailable"
UNAVAILABLE_SUMMARY = (
    "The reviewer did not return a result for this commit. This check is neutral and does not "
    "block merging."
)
NOT_POSTED_SUMMARY = (
    "The reviewer could not post its result. This check is neutral and does not block merging."
)
QUEUE_TITLE = "Merge queue: no new review"
QUEUE_SUMMARY = (
    "Pull requests enter the merge queue only after `xrepo-review` passed on the pull request, "
    "so the merge group gets success without a new review."
)
STARTED_TITLE = "Posting the review result"
STARTED_SUMMARY = "The review finished. Its result is being posted."

_SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
_REPO = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
_PR_NUMBER = re.compile(r"[1-9][0-9]{0,9}")
_NEXT_LINK = re.compile(r'<([^>]+)>\s*;\s*rel="next"')


class GitHubError(Exception):
    """A GitHub API request failed (after retries)."""

    def __init__(self, status: int, message: str) -> None:
        super().__init__(f"HTTP {status}: {message}" if status else message)
        self.status = status


# ---------------------------------------------------------------------------------------------
# GitHub REST client
# ---------------------------------------------------------------------------------------------


def retry_wait(status: int, headers: Any, text: str, attempt: int) -> float | None:
    """Seconds to wait before the next attempt, or None to give up.

    5xx: exponential backoff. 403 or 429 from a rate limit: Retry-After, else the reset time
    when x-ratelimit-remaining is 0, else at least one minute (GitHub's guidance for secondary
    rate limits). Any other 403 is a permission problem, so it is not retried.
    """
    if attempt >= len(BACKOFF_SECONDS):
        return None
    if status in (500, 502, 503, 504):
        return BACKOFF_SECONDS[attempt]
    if status not in (403, 429):
        return None
    headers = headers if headers is not None else {}
    retry_after = str(headers.get("Retry-After") or "").strip()
    reset = str(headers.get("X-RateLimit-Reset") or "").strip()
    if retry_after.isdigit():
        wait = float(retry_after)
    elif str(headers.get("X-RateLimit-Remaining") or "").strip() == "0" and reset.isdigit():
        wait = float(reset) - time.time() + 1
    elif status == 429 or "rate limit" in text.lower():
        wait = 60.0 * 2**attempt
    else:
        return None
    if wait > MAX_RATE_LIMIT_WAIT:
        return None
    return max(wait, 1.0)


def _short(text: str) -> str:
    try:
        message = json.loads(text).get("message")
    except (ValueError, AttributeError):
        message = None
    return " ".join(str(message or text or "no details").split())[:300]


class GitHub:
    """A small GitHub REST API client for one repository."""

    def __init__(
        self, api_url: str, token: str, repo: str, opener: urllib.request.OpenerDirector | None
    ) -> None:
        self.api_url = api_url.rstrip("/")
        self.token = token
        self.repo = repo
        self.opener = opener or urllib.request.build_opener()

    def request(self, method: str, path: str, body: object = None) -> tuple[Any, Any]:
        """Send one request and return (JSON body or None, response headers)."""
        url = path if path.startswith(self.api_url + "/") else self.api_url + path
        data = None if body is None else json.dumps(body).encode("utf-8")
        headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {self.token}",
            "User-Agent": "xrepo-post-results",
            "X-GitHub-Api-Version": "2022-11-28",
        }
        if data is not None:
            headers["Content-Type"] = "application/json"
        where = url[len(self.api_url) :].split("?", 1)[0]
        attempt = 0
        while True:
            request = urllib.request.Request(url, data=data, headers=headers, method=method)
            try:
                with self.opener.open(request, timeout=TIMEOUT_SECONDS) as response:
                    raw, response_headers = response.read(), response.headers
                break
            except urllib.error.HTTPError as err:
                text = err.read().decode("utf-8", "replace")
                wait = retry_wait(err.code, err.headers, text, attempt)
                if wait is None:
                    raise GitHubError(err.code, f"{method} {where}: {_short(text)}") from None
                problem = f"HTTP {err.code}"
            except OSError as err:  # connection errors and timeouts
                if attempt >= len(BACKOFF_SECONDS):
                    raise GitHubError(0, f"{method} {where}: {err}") from None
                wait, problem = BACKOFF_SECONDS[attempt], type(err).__name__
            attempt += 1
            print(f"GitHub API {method} {where}: {problem}; retrying in {wait:.0f} seconds")
            SLEEP(wait)
        if not raw.strip():
            return None, response_headers
        try:
            return json.loads(raw), response_headers
        except ValueError:
            raise GitHubError(0, f"{method} {where}: the response is not JSON") from None

    def paginate(self, path: str) -> Iterator[dict[str, Any]]:
        """Yield the items of every page, following the Link header."""
        url = path
        for _ in range(MAX_PAGES):
            data, headers = self.request("GET", url)
            for item in data if isinstance(data, list) else []:
                if isinstance(item, dict):
                    yield item
            match = _NEXT_LINK.search(str(headers.get("Link") or ""))
            if match is None or not match.group(1).startswith(self.api_url + "/"):
                return
            url = match.group(1)


# ---------------------------------------------------------------------------------------------
# What to post
# ---------------------------------------------------------------------------------------------


@dataclass
class Plan:
    """The check run, the comment, and the job summary for one run."""

    publish: bool  # post the check run (and the comment) to the pull request
    conclusion: str
    title: str
    summary: str
    text: str = ""
    annotations: list[dict[str, Any]] = field(default_factory=list)
    two_steps: bool = False  # step review: create the check run first, then complete it
    comment: str | None = None
    create_comment: bool = False  # False: only update the existing comment
    job_summary: str = ""


def truncate(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[: limit - 3].rstrip() + "..."


def truncate_bytes(text: str, limit: int) -> str:
    data = text.encode("utf-8")
    if len(data) <= limit:
        return text
    return data[: limit - 3].decode("utf-8", "ignore").rstrip() + "..."


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def clean_annotation(item: object) -> dict[str, Any] | None:
    """Return an annotation that the Checks API accepts, or None."""
    if not isinstance(item, dict):
        return None
    path, start = item.get("path"), item.get("start_line")
    if not isinstance(path, str) or not path.strip(" /") or not _is_int(start) or start < 1:
        return None
    end = item.get("end_line")
    if not _is_int(end) or end < start:
        end = start
    level = item.get("annotation_level")
    title = item.get("title") if isinstance(item.get("title"), str) else ""
    message = item.get("message") if isinstance(item.get("message"), str) else ""
    annotation: dict[str, Any] = {
        "path": path.strip().lstrip("/"),
        "start_line": start,
        "end_line": end,
        "annotation_level": level if level in LEVEL_ORDER else "notice",
        "message": truncate_bytes(message or title or CHECK_NAME, MAX_ANNOTATION_MESSAGE_BYTES),
    }
    if title:
        annotation["title"] = truncate(title, MAX_TITLE)
    return annotation


def clean_annotations(raw: object) -> list[dict[str, Any]]:
    """Valid annotations, highest severity first (stable), at most MAX_ANNOTATIONS."""
    cleaned = [a for a in map(clean_annotation, raw if isinstance(raw, list) else []) if a]
    cleaned.sort(key=lambda a: LEVEL_ORDER[a["annotation_level"]])
    return cleaned[:MAX_ANNOTATIONS]


def with_marker(body: str) -> str:
    """The comment body, starting with the marker that finds it again."""
    if COMMENT_MARKER not in body:
        body = f"{COMMENT_MARKER}\n{body}"
    return truncate(body, MAX_COMMENT)


def load_result(path: str | None) -> tuple[dict[str, Any] | None, str]:
    """Return (result, reason). The result is None when result.json is missing or unusable."""
    if not path:
        return None, "no result.json"
    try:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
    except FileNotFoundError:
        return None, "result.json is missing"
    except (OSError, ValueError) as exc:
        return None, f"result.json cannot be read ({type(exc).__name__})"
    if not isinstance(data, dict) or data.get("status") not in ("completed", "unavailable"):
        return None, "result.json has no review status"
    output = data.get("check_output")
    if not isinstance(output, dict) or not all(
        isinstance(output.get(key), str) for key in ("title", "summary")
    ):
        return None, "result.json has no check output"
    return data, ""


def _job_summary(mode: str, title: str, body: str) -> str:
    note = ""
    if mode in ("shadow", "off"):
        note = f"Mode {mode}: nothing is posted to the pull request.\n\n"
    return f"## {CHECK_NAME}: {title}\n\n{note}{body}\n"


def unavailable_plan(publish: bool, mode: str, reason: str) -> Plan:
    body = f"{UNAVAILABLE_SUMMARY}\n\nReason: {reason}."
    return Plan(
        publish=publish,
        conclusion="neutral",
        title=UNAVAILABLE_TITLE,
        summary=UNAVAILABLE_SUMMARY,
        job_summary=_job_summary(mode, UNAVAILABLE_TITLE, body),
    )


def make_plan(
    mode: str, step: str, result: dict[str, Any] | None, reason: str, head_sha: str
) -> Plan:
    """Decide what to post. Pure function: no I/O."""
    publish = mode not in ("shadow", "off")
    if step == "queue":
        return Plan(
            publish=publish,
            conclusion="success",
            title=QUEUE_TITLE,
            summary=QUEUE_SUMMARY,
            job_summary=_job_summary(mode, QUEUE_TITLE, QUEUE_SUMMARY),
        )
    if step != "review" or result is None:
        return unavailable_plan(publish, mode, reason or "no review for this commit")
    request_id = result.get("request_id")
    if head_sha and isinstance(request_id, str) and not request_id.endswith("@" + head_sha):
        return unavailable_plan(publish, mode, "result.json is for another commit")

    output = result["check_output"]
    completed = result.get("status") == "completed"
    conclusion = result.get("conclusion")
    if not completed or conclusion not in CONCLUSIONS:
        conclusion = "neutral"
    # Only a required repository may fail the check, and only when the result agrees.
    if conclusion == "failure" and not (mode == "required" and result.get("mode") == "required"):
        conclusion = "neutral"
    title = truncate(" ".join(output["title"].split()) or UNAVAILABLE_TITLE, MAX_TITLE)
    text = output.get("text") if isinstance(output.get("text"), str) else ""
    comment = result.get("comment_markdown")
    wants_comment = result.get("publish") is not False and isinstance(comment, str)
    job_summary = result.get("job_summary_markdown")
    if not isinstance(job_summary, str) or not job_summary.strip():
        job_summary = _job_summary(mode, title, output["summary"])
    return Plan(
        publish=publish,
        conclusion=conclusion,
        title=title,
        summary=truncate(output["summary"], MAX_OUTPUT_TEXT) or title,
        text=truncate(text, MAX_OUTPUT_TEXT),
        annotations=clean_annotations(output.get("annotations")) if completed else [],
        two_steps=True,
        comment=with_marker(comment) if wants_comment and comment.strip() else None,
        create_comment=completed,
        job_summary=job_summary,
    )


# ---------------------------------------------------------------------------------------------
# Posting
# ---------------------------------------------------------------------------------------------


class Outputs:
    """Step outputs, appended to $GITHUB_OUTPUT as soon as they are known."""

    def __init__(self, path: str | None) -> None:
        self.path = path
        self.values: dict[str, str] = {}

    def set(self, key: str, value: str) -> None:
        self.values[key] = value
        line = f"{key}={value}\n"
        if self.path:
            with open(self.path, "a", encoding="utf-8") as handle:
                handle.write(line)
        else:
            sys.stdout.write(line)


def _id(data: object) -> int:
    value = data.get("id") if isinstance(data, dict) else None
    if not _is_int(value):
        raise GitHubError(0, "the response has no id")
    return value


def complete_check(
    client: GitHub, check_id: int, plan: Plan, annotations: list[dict[str, Any]]
) -> None:
    """Complete the check run. Annotation chunks before the last go in earlier requests."""
    path = f"/repos/{client.repo}/check-runs/{check_id}"
    size = max(1, ANNOTATIONS_PER_REQUEST)
    chunks = [annotations[i : i + size] for i in range(0, len(annotations), size)] or [[]]
    for chunk in chunks[:-1]:
        output = {"title": plan.title, "summary": plan.summary, "annotations": chunk}
        client.request("PATCH", path, {"output": output})
    final: dict[str, Any] = {"title": plan.title, "summary": plan.summary}
    if plan.text:
        final["text"] = plan.text
    if chunks[-1]:
        final["annotations"] = chunks[-1]
    client.request(
        "PATCH", path, {"status": "completed", "conclusion": plan.conclusion, "output": final}
    )


def post_check(
    client: GitHub, plan: Plan, head_sha: str, outputs: Outputs, details_url: str | None
) -> None:
    path = f"/repos/{client.repo}/check-runs"
    base: dict[str, Any] = {"name": CHECK_NAME, "head_sha": head_sha}
    if details_url:
        base["details_url"] = details_url
    if not plan.two_steps:
        output = {"title": plan.title, "summary": plan.summary}
        body = {**base, "status": "completed", "conclusion": plan.conclusion, "output": output}
        created, _ = client.request("POST", path, body)
        outputs.set("check_run_id", str(_id(created)))
        outputs.set("conclusion", plan.conclusion)
        return
    output = {"title": STARTED_TITLE, "summary": STARTED_SUMMARY}
    created, _ = client.request("POST", path, {**base, "status": "in_progress", "output": output})
    check_id = _id(created)
    outputs.set("check_run_id", str(check_id))
    try:
        complete_check(client, check_id, plan, plan.annotations)
    except GitHubError as first:
        print(f"Could not complete the check run ({first}); trying again without annotations")
        try:
            complete_check(client, check_id, plan, [])
        except GitHubError:
            fallback = Plan(True, "neutral", UNAVAILABLE_TITLE, NOT_POSTED_SUMMARY)
            complete_check(client, check_id, fallback, [])
            outputs.set("conclusion", "neutral")
            raise first from None
    outputs.set("conclusion", plan.conclusion)


def _is_ours(comment: Mapping[str, Any]) -> bool:
    """A comment with the marker, written by a bot (people may quote the marker)."""
    user = comment.get("user") if isinstance(comment.get("user"), dict) else {}
    body = comment.get("body")
    return (
        isinstance(body, str)
        and COMMENT_MARKER in body
        and user.get("type") == "Bot"
        and _is_int(comment.get("id"))
    )


def upsert_comment(client: GitHub, number: int, body: str, *, create: bool) -> int | None:
    """Create or update the one comment with the marker. Duplicates of the same bot go away."""
    listing = f"/repos/{client.repo}/issues/{number}/comments?per_page=100"
    ours = [c for c in client.paginate(listing) if _is_ours(c)]
    if ours:
        keep = ours[0]  # the oldest, so the comment keeps its place in the conversation
        if keep.get("body") != body:
            path = f"/repos/{client.repo}/issues/comments/{keep['id']}"
            client.request("PATCH", path, {"body": body})
        login = keep["user"].get("login")
        for extra in ours[1:]:
            if extra["user"].get("login") == login:
                client.request("DELETE", f"/repos/{client.repo}/issues/comments/{extra['id']}")
        return int(keep["id"])
    if not create:
        return None
    path = f"/repos/{client.repo}/issues/{number}/comments"
    created, _ = client.request("POST", path, {"body": body})
    return _id(created)


def post(
    plan: Plan,
    client: GitHub,
    head_sha: str,
    pr_number: int | None,
    outputs: Outputs,
    details_url: str | None,
) -> list[str]:
    """Post the check run and the comment. Returns the problems (empty when all worked)."""
    errors = []
    try:
        post_check(client, plan, head_sha, outputs, details_url)
    except GitHubError as exc:
        errors.append(f"check run: {exc}")
    if plan.comment and pr_number:
        try:
            comment_id = upsert_comment(client, pr_number, plan.comment, create=plan.create_comment)
            if comment_id is not None:
                outputs.set("comment_id", str(comment_id))
        except GitHubError as exc:
            errors.append(f"comment: {exc}")
    return errors


# ---------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------


def parse_args(argv: list[str] | None, environ: Mapping[str, str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Post the xrepo-review check and comment.")
    parser.add_argument("--result", default=environ.get("XREPO_RESULT"), help="result.json")
    parser.add_argument("--mode", default=environ.get("XREPO_MODE", ""), help="repository mode")
    parser.add_argument("--step", default=environ.get("XREPO_STEP", ""), help="review step")
    parser.add_argument("--head-sha", default=environ.get("XREPO_HEAD_SHA", ""), help="commit")
    parser.add_argument(
        "--pr-number", default=environ.get("XREPO_PR_NUMBER", ""), help="pull request number"
    )
    return parser.parse_args(argv)


def _escape(text: str) -> str:
    return text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def details_url(environ: Mapping[str, str], repo: str) -> str | None:
    run_id = environ.get("GITHUB_RUN_ID", "")
    if not run_id.isdigit():
        return None
    server = (environ.get("GITHUB_SERVER_URL") or "https://github.com").rstrip("/")
    return f"{server}/{repo}/actions/runs/{run_id}"


def write_summary(path: str | None, text: str) -> None:
    if not text:
        return
    if path:
        with open(path, "a", encoding="utf-8") as handle:
            handle.write(text.rstrip() + "\n")
    else:
        print(text)


def main(
    argv: list[str] | None = None,
    environ: Mapping[str, str] | None = None,
    opener: urllib.request.OpenerDirector | None = None,
) -> int:
    environ = os.environ if environ is None else environ
    options = parse_args(argv, environ)
    mode = str(options.mode).strip().lower()
    mode = mode if mode in MODES else "unknown"
    step = str(options.step).strip().lower()
    step = step if step in STEPS else "unavailable"
    head_sha = str(options.head_sha).strip().lower()
    number = str(options.pr_number).strip()
    pr_number = int(number) if _PR_NUMBER.fullmatch(number) else None
    result, reason = load_result(options.result) if step == "review" else (None, "")
    plan = make_plan(mode, step, result, reason, head_sha)
    if reason:
        print(f"xrepo post-results: {reason}")

    outputs = Outputs(environ.get("GITHUB_OUTPUT"))
    errors: list[str] = []
    try:
        write_summary(environ.get("GITHUB_STEP_SUMMARY"), plan.job_summary)
    except OSError as exc:
        errors.append(f"job summary: {exc}")
    if plan.publish:
        token = environ.get("GITHUB_TOKEN") or environ.get("GH_TOKEN") or ""
        repo = environ.get("GITHUB_REPOSITORY", "")
        if not token:
            errors.append("no GitHub token: set GITHUB_TOKEN or GH_TOKEN")
        if not _REPO.fullmatch(repo):
            errors.append("GITHUB_REPOSITORY must look like owner/name")
        if not _SHA.fullmatch(head_sha):
            errors.append("head_sha must be a full commit SHA")
        if token and _REPO.fullmatch(repo) and _SHA.fullmatch(head_sha):
            api_url = environ.get("GITHUB_API_URL") or ("https://" + "api.github.com")
            client = GitHub(api_url, token, repo, opener)
            errors += post(plan, client, head_sha, pr_number, outputs, details_url(environ, repo))
    posted = plan.conclusion if plan.publish else "job summary only"
    print(f"xrepo post-results: mode {mode}, step {step}: {posted}")
    for error in errors:
        print(f"::warning title=xrepo post-results::{_escape(error)}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
