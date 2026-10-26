#!/usr/bin/env python3
"""build-payload: pack one pull request for the xrepo Review API.

The review workflow (review.yml) runs this script through the build-payload composite action,
after actions/checkout fetched the full history of the pull request head. It needs only the
Python 3 standard library (3.9 or newer) and the git CLI. File contents come from Git objects,
never from the working tree, so untracked files and files outside the repository are never sent.

Output folder (default: $RUNNER_TEMP/xrepo/payload):

    request.tar.gz   request.json, files/base/<path>, files/head/<path>, diff.patch, and
                     bundles/{openapi,events,knowledge}/{base,head}/<path>
    request.json     the same request.json, for the body of POST /v1/reviews/upload
    infra.tar.gz     infra/{base,head}/<path> for each changed Terraform root. Written only when
                     a root changed. Terraform files never go into request.tar.gz.

Rules:
- "base" is the merge base of the base commit and the head commit, so commits that reached the
  base branch after the pull request started are not part of the review.
- Never packed, and listed in skipped instead: symbolic links, submodules, .git folders,
  secret-looking files (*.pem, *.key, .env*, id_rsa*, ...), and unsupported file names.
- Each archive stays at or under limits.max_archive_bytes, counted before compression. When
  files do not fit, they are added in priority order and the rest is listed in skipped:
  changed specs, schemas, and knowledge concepts first; then other changed files; unchanged
  specs and schemas; documentation; tests; generated code; lock files; vendored code; and
  binary files last.
- Archives are deterministic: sorted names, mtime 0, mode 644, no owner names.

Inputs: command-line options, or the environment variables that action.yml sets (see
parse_args). Outputs ($GITHUB_OUTPUT): request, request_json, infra, has_infra, request_id,
files, skipped. On any problem the script prints a clear message and exits with 1; the review
workflow then posts a neutral check.
"""

from __future__ import annotations

import argparse
import fnmatch
import gzip
import io
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from collections import defaultdict
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import unquote

DEFAULT_MAX_ARCHIVE_BYTES = 100 * 1024 * 1024
DIFF_LIMIT_BYTES = 5 * 1024 * 1024
MAX_MEMBERS = 40_000  # the Review API accepts at most 50,000 members per archive
MAX_BUNDLE_FILES = 5_000  # per bundle kind and side
MAX_LINKS = 20
MAX_DIFF_ARGS_BYTES = 64 * 1024  # pathspecs per git diff call
MAX_NAME_LENGTH = 3_000  # archive member names must stay under 4,096 characters
TERRAFORM_GET_TIMEOUT_SECONDS = 600
SIDES = ("base", "head")

# Fill order when an archive is over the limit: higher numbers are added first.
BUNDLE, SOURCE, CONTEXT, DOCS, TEST, GENERATED, LOCK, VENDORED, BINARY = 8, 7, 6, 5, 4, 3, 2, 1, 0
CATEGORY_PRIORITY = {
    "source": SOURCE,
    "docs": DOCS,
    "test": TEST,
    "generated": GENERATED,
    "lock": LOCK,
    "vendored": VENDORED,
    "binary": BINARY,
}
CATEGORY_LABEL = {
    "source": "changed file",
    "docs": "documentation",
    "test": "test file",
    "generated": "generated code",
    "lock": "lock file",
    "vendored": "vendored code",
    "binary": "binary file",
}

# Matched against the lowercase file name. Never sent; listed in skipped.
SECRET_NAMES = (
    "*.pem", "*.key", "*.p12", "*.pfx", "*.jks", "*.keystore", ".env*", "id_rsa*", "id_dsa*",
    "id_ecdsa*", "id_ed25519*", ".netrc", ".npmrc", ".pypirc", "credentials*.json",
    "service-account*.json", "*.tfstate", "*.tfstate.*",
)  # fmt: skip
# Terraform files go only into infra.tar.gz (the inbox bucket, deleted after 1 day).
TERRAFORM_NAMES = (
    "*.tf", "*.tf.json", "*.tfvars", "*.tfvars.json", "*.tftest.hcl", "*.tftest.json",
    ".terraform.lock.hcl", ".terraformrc", "terraform.rc",
)  # fmt: skip

BINARY_EXTENSIONS = frozenset({
    ".png", ".jpg", ".jpeg", ".gif", ".bmp", ".ico", ".webp", ".tif", ".tiff", ".psd", ".pdf",
    ".zip", ".gz", ".tgz", ".bz2", ".xz", ".7z", ".rar", ".jar", ".war", ".ear", ".class", ".so",
    ".dylib", ".dll", ".exe", ".bin", ".o", ".a", ".woff", ".woff2", ".ttf", ".otf", ".eot",
    ".mp3", ".mp4", ".mov", ".avi", ".wav", ".ogg", ".webm", ".wasm", ".pyc", ".sqlite", ".db",
})  # fmt: skip
VENDORED_FOLDERS = frozenset({
    "vendor", "third_party", "third-party", "thirdparty", "node_modules", "bower_components",
    "pods", "carthage",
})  # fmt: skip
LOCK_FILES = frozenset({
    "package-lock.json", "npm-shrinkwrap.json", "yarn.lock", "pnpm-lock.yaml", "bun.lockb",
    "go.sum", "go.work.sum", "cargo.lock", "poetry.lock", "pipfile.lock", "uv.lock", "pdm.lock",
    "gemfile.lock", "composer.lock", "gradle.lockfile", "packages.lock.json", "mix.lock",
    "pubspec.lock", "podfile.lock", "flake.lock",
})  # fmt: skip
GENERATED_FOLDERS = frozenset({"generated", "__generated__", "dist"})
GENERATED_NAME = re.compile(  # matched against the lowercase name
    r"(\.pb\.(go|cc|h|ts|js)|_pb2(_grpc)?\.pyi?|\.pb\.gw\.go|\.gen\.(go|ts|js)"
    r"|[._-]generated\.[a-z0-9]+|\.g\.dart|\.freezed\.dart|\.designer\.cs|\.min\.(js|css)"
    r"|\.(js|css)\.map)$"
)
TEST_FOLDERS = frozenset({
    "test", "tests", "__tests__", "testdata", "test-data", "testing", "fixtures", "__fixtures__",
    "__snapshots__", "__mocks__", "e2e",
})  # fmt: skip
TEST_NAME = re.compile(  # matched against the name as written (Java and Kotlin use CamelCase)
    r"(_test\.go|_test\.py|^test_.*\.py|[A-Za-z0-9](Test|Tests|IT|TestCase)\.(java|kt|scala|groovy)"
    r"|\.(test|spec)\.(js|jsx|ts|tsx|mjs|cjs)|_spec\.rb|\.snap)$"
)
DOC_EXTENSIONS = frozenset({".md", ".markdown", ".mdx", ".rst", ".adoc", ".asciidoc", ".txt"})
DOC_FOLDERS = frozenset({"docs", "doc", "documentation"})

DIFF_OPTIONS = (
    "--no-color", "--no-ext-diff", "--no-textconv", "--no-relative", "--full-index",
    "--src-prefix=a/", "--dst-prefix=b/", "--diff-algorithm=myers", "--indent-heuristic",
    "--unified=3", "--inter-hunk-context=0", "--submodule=short", "-M",
)  # fmt: skip

_SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
_REPO = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
_BRANCH = re.compile(r"[A-Za-z0-9._/+-]{1,255}")
_BAD_NAME_CHARS = re.compile(r"[\x00-\x1f\x7f\\]")
_HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
_DEPENDS_ON = re.compile(r"^[ \t>*_+-]*depends[- ]on[ \t*_]*:(?P<refs>.*)$", re.I | re.M)
_LINK = re.compile(
    r"https?://[^\s/]+/(?P<u_owner>[A-Za-z0-9_.-]+)/(?P<u_name>[A-Za-z0-9_.-]+)/pull/"
    r"(?P<u_number>[0-9]+)"
    r"|(?<![\w./#-])(?P<owner>[A-Za-z0-9_.-]+)/(?P<name>[A-Za-z0-9_.-]+)#(?P<number>[0-9]+)"
    r"|(?<![\w/#&])#(?P<local>[0-9]+)"
)
_REF_VALUE = re.compile(r"""["']?\$ref["']?\s*:\s*(?:"([^"]*)"|'([^']*)'|([^\s,}\]]+))""")
_MODULE_BLOCK = re.compile(r'(?m)^[ \t]*module[ \t]+"[^"]*"[ \t]*\{')
_MODULE_SOURCE = re.compile(r'(?m)^[ \t]*source[ \t]*=[ \t]*"([^"]+)"')
_STATUS = {"A": "added", "C": "added", "D": "removed", "M": "modified", "T": "modified"}


class PayloadError(Exception):
    """A problem that stops the build. The message says what to fix."""


# ---------------------------------------------------------------------------------------------
# Paths, names, and globs
# ---------------------------------------------------------------------------------------------


def decode_path(raw: bytes) -> str:
    """Decode a Git path. Bytes that are not UTF-8 survive as surrogates (see name_problem)."""
    return raw.decode("utf-8", "surrogateescape")


def display(path: str) -> str:
    """Return a printable form of a path (invalid UTF-8 becomes U+FFFD)."""
    return path.encode("utf-8", "surrogateescape").decode("utf-8", "replace")


def log_text(text: str) -> str:
    """Remove control characters, so that a file name cannot start a workflow command."""
    return re.sub(r"[\x00-\x1f\x7f]", "?", display(text))


def name_problem(path: str) -> str | None:
    """Return why a path cannot go into an archive, or None."""
    if any("\udc80" <= char <= "\udcff" for char in path):
        return "file name is not valid UTF-8"
    if _BAD_NAME_CHARS.search(path):
        return "file name has a backslash or a control character"
    if len(path) > MAX_NAME_LENGTH:
        return "file name is too long"
    if ".git" in path.split("/"):
        return ".git folder"
    return None


def _name_matches(path: str, patterns: Iterable[str]) -> bool:
    name = posixpath.basename(path).lower()
    return any(fnmatch.fnmatchcase(name, pattern) for pattern in patterns)


def is_secret(path: str) -> bool:
    """True for file names that usually hold keys or credentials."""
    return _name_matches(path, SECRET_NAMES)


def is_terraform(path: str) -> bool:
    """True for Terraform configuration, variable, and working files."""
    return ".terraform" in path.split("/")[:-1] or _name_matches(path, TERRAFORM_NAMES)


def normalize(path: str) -> str | None:
    """Return a repository-relative path, or None when it points outside the repository."""
    path = path.strip().replace("\\", "/")
    if not path or path.startswith("/"):
        return None
    norm = posixpath.normpath(path)
    if norm == ".." or norm.startswith("../"):
        return None
    return norm


def under(path: str, folder: str) -> bool:
    return folder == "." or path == folder or path.startswith(folder + "/")


def category(path: str) -> str:
    """Classify a changed file for the fill order (see CATEGORY_PRIORITY)."""
    parts = path.split("/")
    name, lower = parts[-1], parts[-1].lower()
    folders = {part.lower() for part in parts[:-1]}
    extension = posixpath.splitext(lower)[1]
    if extension in BINARY_EXTENSIONS:
        return "binary"
    if folders & VENDORED_FOLDERS:
        return "vendored"
    if lower in LOCK_FILES or lower.endswith((".lock", ".lockfile")):
        return "lock"
    if folders & GENERATED_FOLDERS or GENERATED_NAME.search(lower):
        return "generated"
    if folders & TEST_FOLDERS or TEST_NAME.search(name):
        return "test"
    if extension in DOC_EXTENSIONS or folders & DOC_FOLDERS:
        return "docs"
    return "source"


def glob_regex(pattern: str) -> re.Pattern[str]:
    """Compile a glob relative to the repository root.

    `**` as a whole path segment matches any number of folders (also none), `*` and `?` stay
    inside one folder, and `[...]` is a character class (`[!...]` negates it).
    """
    pattern = pattern.strip()
    while pattern.startswith("./"):
        pattern = pattern[2:]
    pattern = pattern.lstrip("/")
    out: list[str] = []
    i, n = 0, len(pattern)
    while i < n:
        char = pattern[i]
        if char == "*":
            j = i
            while j < n and pattern[j] == "*":
                j += 1
            whole_segment = (i == 0 or pattern[i - 1] == "/") and (j == n or pattern[j] == "/")
            if j - i >= 2 and whole_segment:
                out.append(".*" if j == n else "(?:[^/]*/)*")
                i = j if j == n else j + 1
            else:
                out.append("[^/]*")
                i = j
        elif char == "?":
            out.append("[^/]")
            i += 1
        elif char == "[":
            j = i + 1
            if j < n and pattern[j] in "!^":
                j += 1
            if j < n and pattern[j] == "]":
                j += 1
            end = pattern.find("]", j)
            if end < 0:
                out.append(re.escape(char))
                i += 1
                continue
            body = pattern[i + 1 : end]
            negate = body[:1] in ("!", "^")
            if negate:
                body = body[1:]
            for special in ("\\", "[", "&", "~", "|"):
                body = body.replace(special, "\\" + special)
            out.append("(?!/)[" + ("^" if negate else "") + body + "]")
            i = end + 1
        else:
            out.append(re.escape(char))
            i += 1
    return re.compile("".join(out))


class Globs:
    """A list of repository globs from repo-config."""

    def __init__(self, patterns: object) -> None:
        items = patterns if isinstance(patterns, list) else []
        self.regexes = [glob_regex(p) for p in items if isinstance(p, str) and p.strip()]

    def __bool__(self) -> bool:
        return bool(self.regexes)

    def match(self, path: str) -> bool:
        return any(regex.fullmatch(path) for regex in self.regexes)


# ---------------------------------------------------------------------------------------------
# Pull request description, OpenAPI references, Terraform module sources
# ---------------------------------------------------------------------------------------------


def parse_links(body: str, repo: str, number: int) -> list[str]:
    """Return linked pull requests from `Depends-On:` lines, as owner/repo#number.

    Accepts owner/repo#123, a pull request URL, and #123 (this repository). HTML comments are
    ignored, so examples in a pull request template do not count. At most MAX_LINKS links.
    """
    owner_here, name_here = repo.split("/", 1)
    seen = {f"{repo}#{number}".lower()}
    links: list[str] = []
    for line in _DEPENDS_ON.finditer(_HTML_COMMENT.sub("", body or "")):
        for ref in _LINK.finditer(line.group("refs")):
            if ref.group("u_number"):
                owner, name, digits = ref.group("u_owner", "u_name", "u_number")
            elif ref.group("number"):
                owner, name, digits = ref.group("owner", "name", "number")
            else:
                owner, name, digits = owner_here, name_here, ref.group("local")
            if owner in (".", "..") or name in (".", "..") or len(digits) > 9 or int(digits) < 1:
                continue
            link = f"{owner}/{name}#{int(digits)}"
            if link.lower() in seen:
                continue
            seen.add(link.lower())
            links.append(link)
            if len(links) == MAX_LINKS:
                return links
    return links


def ref_targets(text: str) -> list[str]:
    """Return the file part of every relative `$ref` in a YAML or JSON document."""
    targets = []
    for match in _REF_VALUE.finditer(text):
        value = (match.group(1) or match.group(2) or match.group(3) or "").strip()
        file_part = value.split("#", 1)[0]
        if not file_part or "://" in file_part or file_part.startswith(("/", "urn:")):
            continue
        targets.append(unquote(file_part))
    return targets


def _block_end(text: str, start: int) -> int:
    """Return the index after the brace that closes the block opened just before start."""
    depth, i, n = 1, start, len(text)
    while i < n:
        char = text[i]
        if char == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif char == "#" or text.startswith("//", i):
            newline = text.find("\n", i)
            i = n if newline < 0 else newline
        elif text.startswith("/*", i):
            close = text.find("*/", i + 2)
            i = n if close < 0 else close + 1
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return n


def module_sources(text: str, *, json_format: bool = False) -> list[str]:
    """Return the `source` of every module block in a .tf (or .tf.json) file."""
    sources: list[str] = []
    if json_format:
        try:
            data = json.loads(text)
        except ValueError:
            return sources
        blocks = data.get("module") if isinstance(data, dict) else None
        for item in blocks if isinstance(blocks, list) else [blocks]:
            for module in item.values() if isinstance(item, dict) else []:
                if isinstance(module, dict) and isinstance(module.get("source"), str):
                    sources.append(module["source"])
        return sources
    for match in _MODULE_BLOCK.finditer(text):
        found = _MODULE_SOURCE.search(text[match.end() : _block_end(text, match.end())])
        if found:
            sources.append(found.group(1))
    return sources


# ---------------------------------------------------------------------------------------------
# Git
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Entry:
    """One file of a commit (git ls-tree -l)."""

    mode: str
    kind: str
    oid: str
    size: int

    def problem(self) -> str | None:
        """Return why the file cannot be packed, or None for a regular file."""
        if self.kind == "commit" or self.mode == "160000":
            return "submodule"
        if self.mode == "120000":
            return "symbolic link"
        if self.kind != "blob" or not self.mode.startswith("100"):
            return "not a regular file"
        return None


@dataclass(frozen=True)
class Change:
    """One changed file (git diff --name-status -M)."""

    path: str
    status: str  # added, modified, removed, renamed
    previous_path: str | None = None

    @property
    def base_path(self) -> str | None:
        if self.status == "added":
            return None
        return self.previous_path if self.status == "renamed" else self.path

    @property
    def head_path(self) -> str | None:
        return None if self.status == "removed" else self.path


def parse_name_status(output: bytes) -> list[Change]:
    """Parse `git diff --name-status -z -M` output."""
    tokens = output.split(b"\0")
    changes: list[Change] = []
    i = 0
    while i < len(tokens) and tokens[i]:
        letter = tokens[i][:1].decode("ascii", "replace")
        i += 1
        if letter in ("R", "C"):
            if i + 1 >= len(tokens):
                break
            old, new = decode_path(tokens[i]), decode_path(tokens[i + 1])
            i += 2
            changes.append(Change(new, "renamed", old) if letter == "R" else Change(new, "added"))
        else:
            if i >= len(tokens):
                break
            changes.append(Change(decode_path(tokens[i]), _STATUS.get(letter, "modified")))
            i += 1
    return changes


class Git:
    """The git CLI in the checked-out repository."""

    def __init__(self, repo: Path) -> None:
        self.repo = repo
        self.env = dict(os.environ, GIT_TERMINAL_PROMPT="0", LC_ALL="C")
        self._batch: subprocess.Popen[bytes] | None = None

    def run(self, *args: str, check: bool = True) -> bytes:
        proc = subprocess.run(
            ["git", *args], cwd=self.repo, env=self.env, capture_output=True, check=False
        )
        if check and proc.returncode != 0:
            lines = proc.stderr.decode("utf-8", "replace").strip().splitlines()
            detail = lines[-1] if lines else f"exit code {proc.returncode}"
            command = next((a for a in args if not a.startswith("-")), "")
            raise PayloadError(f"git {command} failed: {log_text(detail)}")
        return proc.stdout

    def commit(self, rev: str) -> str | None:
        """Return the full SHA of a commit, or None when it is not in the repository."""
        commit_ref = f"{rev}^" + "{commit}"
        output = self.run(
            "rev-parse", "--verify", "--quiet", "--end-of-options", commit_ref, check=False
        )
        sha = output.decode("ascii", "replace").strip()
        return sha if _SHA.fullmatch(sha) else None

    def merge_base(self, first: str, second: str) -> str | None:
        sha = self.run("merge-base", first, second, check=False).decode("ascii", "replace").strip()
        return sha if _SHA.fullmatch(sha) else None

    def tree(self, commit: str) -> dict[str, Entry]:
        entries: dict[str, Entry] = {}
        for item in self.run("ls-tree", "-r", "-z", "-l", "--full-tree", commit).split(b"\0"):
            if not item:
                continue
            meta, _, raw = item.partition(b"\t")
            mode, kind, oid, size = meta.decode("ascii").split()
            entries[decode_path(raw)] = Entry(mode, kind, oid, int(size) if size.isdigit() else 0)
        return entries

    def changes(self, base: str, head: str) -> list[Change]:
        output = self.run(
            "diff", "--name-status", "-z", "-M", "--no-relative", "--no-ext-diff", base, head, "--"
        )
        return parse_name_status(output)

    def diff(self, base: str, head: str, groups: list[tuple[str, ...]]) -> bytes:
        """Unified diff of the given paths. Both paths of a rename stay in the same call."""
        chunks: list[bytes] = []
        batch: list[str] = []
        size = 0
        for group in groups:
            cost = sum(len(p.encode("utf-8", "surrogateescape")) + 1 for p in group)
            if batch and size + cost > MAX_DIFF_ARGS_BYTES:
                chunks.append(self._diff(base, head, batch))
                batch, size = [], 0
            batch.extend(group)
            size += cost
        if batch:
            chunks.append(self._diff(base, head, batch))
        return b"".join(chunks)

    def _diff(self, base: str, head: str, paths: list[str]) -> bytes:
        return self.run("--literal-pathspecs", "diff", *DIFF_OPTIONS, base, head, "--", *paths)

    def read(self, oid: str) -> bytes:
        """Return the content of a blob (one git cat-file --batch process for all reads)."""
        if self._batch is None:
            self._batch = subprocess.Popen(
                ["git", "cat-file", "--batch"],
                cwd=self.repo,
                env=self.env,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
            )
        assert self._batch.stdin is not None and self._batch.stdout is not None
        self._batch.stdin.write(oid.encode("ascii") + b"\n")
        self._batch.stdin.flush()
        header = self._batch.stdout.readline().split()
        if len(header) != 3 or header[1] != b"blob":
            raise PayloadError(f"cannot read Git object {oid}")
        size = int(header[2])
        data = self._batch.stdout.read(size)
        self._batch.stdout.read(1)  # the newline after the content
        if len(data) != size:
            raise PayloadError(f"Git object {oid} is truncated")
        return data

    def close(self) -> None:
        if self._batch is not None:
            assert self._batch.stdin is not None
            self._batch.stdin.close()
            self._batch.wait(timeout=60)
            self._batch = None


# ---------------------------------------------------------------------------------------------
# Archives
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Member:
    """One archive member. The content comes from a Git blob, a file, or memory."""

    name: str
    size: int
    oid: str | None = None
    file: str | None = None
    data: bytes | None = None


@dataclass
class Unit:
    """Members that are kept or dropped together (for example base and head of one path)."""

    key: tuple[str, str]
    priority: int
    reason: str
    paths: list[str]
    members: list[Member]
    size: int = field(init=False)

    def __post_init__(self) -> None:
        self.size = sum(tar_member_size(m.name, m.size) for m in self.members)


def tar_info(name: str, size: int) -> tarfile.TarInfo:
    info = tarfile.TarInfo(name)
    info.size = size
    info.mode = 0o644
    info.mtime = 0
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    info.type = tarfile.REGTYPE
    return info


def tar_member_size(name: str, size: int) -> int:
    """Bytes that one member takes in the tar stream (headers and padded content)."""
    header = tar_info(name, size).tobuf(tarfile.PAX_FORMAT, "utf-8", "surrogateescape")
    return len(header) + -(-size // tarfile.BLOCKSIZE) * tarfile.BLOCKSIZE


def tar_budget(limit: int) -> int:
    """Tar bytes (before compression) that fit in an archive of at most limit bytes.

    Leaves room for the end-of-archive records and for gzip overhead on data that does not
    compress, so the .tar.gz file is never larger than limit.
    """
    return limit - 2 * tarfile.RECORDSIZE - limit // 1000 - 1024


def write_archive(path: Path, members: Iterable[Member], read: Callable[[Member], bytes]) -> int:
    """Write a deterministic tar.gz and return its size in bytes."""
    unique = {member.name: member for member in members}
    with (
        open(path, "wb") as raw,
        gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz,
        tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT, encoding="utf-8") as tar,
    ):
        for name in sorted(unique):
            data = read(unique[name])
            if len(data) != unique[name].size:
                raise PayloadError(f"{log_text(name)} changed while it was packed")
            tar.addfile(tar_info(name, len(data)), io.BytesIO(data))
    return path.stat().st_size


def cut_diff(data: bytes, limit: int) -> bytes:
    """Cut a diff at a line end so that it fits in limit bytes, and add a note."""
    if len(data) <= limit:
        return data
    note = (
        f"\n# xrepo: diff.patch was cut at {limit} bytes. files/base and files/head hold the "
        "complete files.\n"
    ).encode()
    cut = data[: max(0, limit - len(note))]
    return cut[: cut.rfind(b"\n") + 1] + note


# ---------------------------------------------------------------------------------------------
# Inputs
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class InfraRoot:
    path: str
    var_files: tuple[str, ...]


@dataclass
class Config:
    """The parts of GET /v1/repo-config that build-payload uses."""

    openapi: list[str]
    schemas: Globs
    knowledge: Globs
    infra_roots: list[InfraRoot]
    config_version: str
    max_archive_bytes: int


@dataclass(frozen=True)
class PullRequest:
    number: int
    head_sha: str
    base_sha: str | None
    base_ref: str | None
    body: str


def read_json(path: str | None, what: str) -> object:
    if not path:
        raise PayloadError(f"{what}: no file given")
    try:
        with open(path, encoding="utf-8") as handle:
            return json.load(handle)
    except OSError as exc:
        raise PayloadError(f"{what}: cannot read {path}: {exc.strerror}") from None
    except ValueError as exc:
        raise PayloadError(f"{what}: {path} is not valid JSON: {exc}") from None


def read_config(path: str | None) -> Config:
    data = read_json(path, "config")
    if not isinstance(data, dict):
        raise PayloadError("config: expected the JSON object from GET /v1/repo-config")
    limits = data.get("limits")
    max_bytes = limits.get("max_archive_bytes") if isinstance(limits, dict) else None
    if isinstance(max_bytes, bool) or not isinstance(max_bytes, int) or max_bytes <= 0:
        max_bytes = DEFAULT_MAX_ARCHIVE_BYTES
    roots = []
    raw_roots = data.get("infra_roots")
    for item in raw_roots if isinstance(raw_roots, list) else []:
        if not isinstance(item, dict) or not isinstance(item.get("path"), str):
            continue
        var_files: list[str] = []
        environments = item.get("environments")
        for environment in environments.values() if isinstance(environments, dict) else []:
            names = environment.get("var_files") if isinstance(environment, dict) else None
            var_files += [n for n in names if isinstance(n, str)] if isinstance(names, list) else []
        roots.append(InfraRoot(item["path"], tuple(var_files)))
    openapi = data.get("openapi")
    version = data.get("config_version")
    return Config(
        openapi=[p for p in openapi if isinstance(p, str)] if isinstance(openapi, list) else [],
        schemas=Globs(data.get("kafka_schema_paths")),
        knowledge=Globs(data.get("knowledge_paths")),
        infra_roots=roots,
        config_version=str(version).strip() if version not in (None, "") else "unknown",
        max_archive_bytes=max_bytes,
    )


def read_pr(path: str | None) -> PullRequest:
    data = read_json(path, "pr")
    if not isinstance(data, dict):
        raise PayloadError("pr: expected a JSON object")
    number = data.get("number")
    if isinstance(number, str) and number.isdigit():
        number = int(number)
    if isinstance(number, bool) or not isinstance(number, int) or number < 1:
        raise PayloadError("pr: number must be a positive integer (only pull requests)")
    head = data.get("head_sha")
    if not isinstance(head, str) or not _SHA.fullmatch(head):
        raise PayloadError("pr: head_sha must be a full commit SHA")
    base = data.get("base_sha")
    base_ref = data.get("base_ref")
    body = data.get("body")
    branch_ok = isinstance(base_ref, str) and _BRANCH.fullmatch(base_ref) and ".." not in base_ref
    return PullRequest(
        number=number,
        head_sha=head,
        base_sha=base if isinstance(base, str) and _SHA.fullmatch(base) else None,
        base_ref=base_ref if branch_ok else None,
        body=body if isinstance(body, str) else "",
    )


# ---------------------------------------------------------------------------------------------
# Builder
# ---------------------------------------------------------------------------------------------


@dataclass
class BuildResult:
    request: Path
    request_json: Path
    infra: Path | None
    request_id: str
    files: int
    skipped: list[dict[str, str]]


class Builder:
    """Builds request.tar.gz and infra.tar.gz for one pull request."""

    def __init__(
        self, git: Git, config: Config, pr: PullRequest, repo: str, force: bool, out_dir: Path
    ) -> None:
        self.git = git
        self.config = config
        self.pr = pr
        self.repo = repo
        self.force = force
        self.out_dir = out_dir
        self.skipped: set[tuple[str, str]] = set()
        self.infra_paths: set[str] = set()  # files of the changed Terraform roots
        self.temp_dirs: list[Path] = []
        self.trees: dict[str, dict[str, Entry]] = {}
        self._indexes: dict[str, dict[str, list[str]]] = {}
        self._folders: dict[str, set[str]] = {}
        self._cache: dict[str, bytes] = {}
        self.head_sha = self.base_sha = self.merge_base_sha = self.request_id = ""

    # -- helpers ------------------------------------------------------------------------------

    def skip(self, path: str, reason: str) -> None:
        self.skipped.add((display(path), reason))

    def allowed(self, path: str, entry: Entry | None, *, record: bool = True) -> bool:
        """True when the file may be packed. Otherwise optionally records why in skipped."""
        if entry is None:
            return False
        problem = name_problem(path)
        if problem is None and is_secret(path):
            problem = "secret-looking file name: never sent"
        if problem is None:
            problem = entry.problem()
        if problem is not None:
            if record:
                self.skip(path, problem)
            return False
        return True

    def text(self, entry: Entry) -> str:
        if entry.oid not in self._cache:
            self._cache[entry.oid] = self.git.read(entry.oid)
        return self._cache[entry.oid].decode("utf-8", "replace")

    def read_member(self, member: Member) -> bytes:
        if member.data is not None:
            return member.data
        if member.file is not None:
            with open(member.file, "rb") as handle:
                return handle.read()
        assert member.oid is not None
        cached = self._cache.get(member.oid)
        return cached if cached is not None else self.git.read(member.oid)

    def differs(self, path: str) -> bool:
        base, head = self.trees["base"].get(path), self.trees["head"].get(path)
        return (base.oid if base else None) != (head.oid if head else None)

    def sides(self, change: Change) -> Iterator[tuple[str, str]]:
        if change.base_path is not None:
            yield "base", change.base_path
        if change.head_path is not None:
            yield "head", change.head_path

    def folders(self, side: str) -> set[str]:
        """Every folder that holds at least one file on this side ("." is the root)."""
        if side not in self._folders:
            folders = {"."}
            for path in self.trees[side]:
                parent = posixpath.dirname(path)
                while parent and parent not in folders:
                    folders.add(parent)
                    parent = posixpath.dirname(parent)
            self._folders[side] = folders
        return self._folders[side]

    def children(self, side: str, folder: str) -> list[str]:
        """Files directly in a folder on this side."""
        if side not in self._indexes:
            index: dict[str, list[str]] = defaultdict(list)
            for path in self.trees[side]:
                index[posixpath.dirname(path) or "."].append(path)
            self._indexes[side] = index
        return self._indexes[side].get(folder, [])

    # -- commits ------------------------------------------------------------------------------

    def resolve_commits(self) -> None:
        head = self.git.commit(self.pr.head_sha)
        if head is None:
            raise PayloadError(
                f"head commit {self.pr.head_sha} is not in the checkout: check out the pull "
                "request head with fetch-depth: 0"
            )
        base = self.git.commit(self.pr.base_sha) if self.pr.base_sha else None
        if base is None and self.pr.base_ref:
            base = self.git.commit(f"refs/remotes/origin/{self.pr.base_ref}")
        if base is None:
            raise PayloadError(
                "base commit is not in the checkout: use actions/checkout with fetch-depth: 0"
            )
        merge_base = self.git.merge_base(base, head)
        if merge_base is None:
            raise PayloadError(
                f"no merge base of {base} and {head}: use actions/checkout with fetch-depth: 0"
            )
        self.head_sha, self.base_sha, self.merge_base_sha = head, base, merge_base

    # -- infra.tar.gz -------------------------------------------------------------------------

    def scan_root(self, root: str, side: str) -> tuple[list[str], bool]:
        """Return the folders of a root and of its local modules on one side, and whether
        any module is remote (a source that does not start with ./ or ../)."""
        tree = self.trees[side]
        found: set[str] = set()
        todo, remote = [root], False
        while todo:
            folder = todo.pop()
            if folder in found or folder not in self.folders(side):
                continue
            found.add(folder)
            for path in self.children(side, folder):
                lower, entry = path.lower(), tree[path]
                if not lower.endswith((".tf", ".tf.json")) or entry.problem() is not None:
                    continue
                json_format = lower.endswith(".json")
                for source in module_sources(self.text(entry), json_format=json_format):
                    if not source.startswith(("./", "../")):
                        remote = True
                        continue
                    target = normalize(posixpath.join(folder, source))
                    if target is None:
                        where = posixpath.join(folder, source)
                        self.skip(where, "local Terraform module outside the repository")
                    else:
                        todo.append(target)
        return sorted(found), remote

    def build_infra(self, changes: list[Change]) -> Path | None:
        """Write infra.tar.gz for the changed Terraform roots. Returns its path or None."""
        changed_paths = {p for c in changes for p in (c.path, c.previous_path) if p}
        roots: dict[str, dict[str, set[str]]] = {}  # root -> side -> repository paths
        remote: dict[str, set[str]] = defaultdict(set)  # side -> roots with remote modules
        for item in self.config.infra_roots:
            root = normalize(item.path)
            if root is None:
                self.skip(item.path, "infra root outside the repository")
                continue
            if root in roots:
                continue
            var_files = []
            for name in item.var_files:
                path = normalize(posixpath.join(root, name))
                if path is None:
                    self.skip(posixpath.join(root, name), "var file outside the repository")
                else:
                    var_files.append(path)
            scanned = {side: self.scan_root(root, side) for side in SIDES}
            watched = {folder for folders, _ in scanned.values() for folder in folders}
            if not any(p in var_files or any(under(p, f) for f in watched) for p in changed_paths):
                continue
            roots[root] = {}
            for side in SIDES:
                folders, uses_remote = scanned[side]
                tree = self.trees[side]
                paths = {p for p in tree if any(under(p, f) for f in folders)}
                paths |= {p for p in var_files if p in tree}
                roots[root][side] = paths
                self.infra_paths |= paths
                if uses_remote and paths:
                    remote[side].add(root)
        if not roots:
            return None

        members: dict[str, Member] = {}
        owners: dict[str, set[str]] = defaultdict(set)  # member name -> roots that need it
        for root, by_side in roots.items():
            for side, paths in by_side.items():
                for path in sorted(paths):
                    if ".terraform" in path.split("/"):
                        self.skip(path, "Terraform working folder (.terraform): not sent")
                        continue
                    entry = self.trees[side][path]
                    if not self.allowed(path, entry):
                        continue
                    name = f"infra/{side}/{path}"
                    members[name] = Member(name, entry.size, oid=entry.oid)
                    owners[name].add(root)
        modules = self.download_modules(remote, members)
        return self.write_infra(set(roots), members, owners, modules)

    def download_modules(
        self, remote: Mapping[str, set[str]], members: Mapping[str, Member]
    ) -> dict[tuple[str, str], list[Member]]:
        """Run terraform get for roots with remote modules and collect .terraform/modules."""
        found: dict[tuple[str, str], list[Member]] = {}
        terraform = shutil.which("terraform")
        for side in SIDES:
            if not remote.get(side):
                continue
            if terraform is None:
                for root in sorted(remote[side]):
                    self.skip(root, "remote Terraform modules not included: terraform not found")
                continue
            work = Path(tempfile.mkdtemp(prefix=f"xrepo-terraform-{side}-", dir=_temp_root()))
            self.temp_dirs.append(work)
            prefix = f"infra/{side}/"
            for name, member in members.items():
                if name.startswith(prefix):
                    target = work / name[len(prefix) :]
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(self.read_member(member))
            env = dict(os.environ, TF_IN_AUTOMATION="1", TF_INPUT="0", CHECKPOINT_DISABLE="1")
            for root in sorted(remote[side]):
                reason = None
                try:
                    proc = subprocess.run(
                        [terraform, f"-chdir={work / root}", "get", "-no-color"],
                        capture_output=True,
                        env=env,
                        timeout=TERRAFORM_GET_TIMEOUT_SECONDS,
                        check=False,
                    )
                    if proc.returncode != 0:
                        lines = proc.stderr.decode("utf-8", "replace").strip().splitlines()
                        detail = log_text(lines[-1]) if lines else str(proc.returncode)
                        print(f"terraform get failed for {log_text(root)} ({side}): {detail}")
                        reason = f"terraform get failed ({side} side)"
                except subprocess.TimeoutExpired:
                    reason = f"terraform get timed out ({side} side)"
                if reason:
                    self.skip(root, f"remote Terraform modules not included: {reason}")
                    continue
                found[(side, root)] = list(_module_members(work, root, side))
        return found

    def write_infra(
        self,
        kept: set[str],
        members: Mapping[str, Member],
        owners: Mapping[str, set[str]],
        modules: dict[tuple[str, str], list[Member]],
    ) -> Path | None:
        """Write infra.tar.gz. Over the limit, downloaded modules go first, then whole roots."""
        budget = tar_budget(self.config.max_archive_bytes)

        def chosen() -> list[Member]:
            files = [m for name, m in members.items() if owners[name] & kept]
            for (_, root), downloaded in sorted(modules.items()):
                if root in kept:
                    files.extend(downloaded)
            return files

        def fits(files: list[Member]) -> bool:
            return _size(files) <= budget and len(files) <= MAX_MEMBERS

        files = chosen()
        for side, root in sorted(modules, key=lambda key: (-_size(modules[key]), key)):
            if fits(files):
                break
            del modules[(side, root)]
            self.skip(
                root, f"remote Terraform modules not included: over the size limit ({side} side)"
            )
            files = chosen()
        while kept and not fits(files):
            sizes = {r: _size(m for n, m in members.items() if r in owners[n]) for r in kept}
            root = min(kept, key=lambda r: (-sizes[r], r))
            kept.discard(root)
            self.skip(root, "Terraform root not sent: over the archive size limit")
            files = chosen()
        if not files:
            return None
        path = self.out_dir / "infra.tar.gz"
        size = write_archive(path, files, self.read_member)
        if size > self.config.max_archive_bytes:
            raise PayloadError(f"infra.tar.gz has {size} bytes, over the limit")
        print(f"infra.tar.gz: {len(files)} files from {len(kept)} Terraform roots, {size} bytes")
        return path

    # -- request.tar.gz -----------------------------------------------------------------------

    def file_units(self, changes: list[Change]) -> tuple[list[Unit], list[tuple[str, ...]]]:
        """files/{base,head}/<path> for each change, and the paths for diff.patch."""
        units: list[Unit] = []
        diff_groups: list[tuple[str, ...]] = []
        for change in changes:
            members: list[Member] = []
            group: list[str] = []
            for side, path in self.sides(change):
                if is_terraform(path):
                    if path not in self.infra_paths:
                        self.skip(path, "Terraform file outside the changed infra roots: not sent")
                    continue
                entry = self.trees[side].get(path)
                if entry is None or not self.allowed(path, entry):
                    continue
                members.append(Member(f"files/{side}/{path}", entry.size, oid=entry.oid))
                if path not in group:
                    group.append(path)
            if group:
                diff_groups.append(tuple(group))
            if members:
                kind = category(change.path)
                units.append(
                    Unit(
                        key=("files", change.path),
                        priority=CATEGORY_PRIORITY[kind],
                        reason=f"over the archive size limit ({CATEGORY_LABEL[kind]})",
                        paths=[change.path],
                        members=members,
                    )
                )
        return units, diff_groups

    def bundle_unit(
        self, kind: str, path: str, sides: Iterable[str], *, changed: bool, record: bool
    ) -> Unit | None:
        members = []
        for side in sides:
            entry = self.trees[side].get(path)
            if entry is None or is_terraform(path) or not self.allowed(path, entry, record=record):
                continue
            members.append(Member(f"bundles/{kind}/{side}/{path}", entry.size, oid=entry.oid))
        if not members:
            return None
        return Unit(
            key=(kind, path),
            priority=BUNDLE if changed else CONTEXT,
            reason=f"over the archive size limit ({kind} bundle{'' if changed else ', unchanged'})",
            paths=[path],
            members=members,
        )

    def openapi_units(self) -> list[Unit]:
        """Every spec in repo-config openapi plus its relative $ref targets, on both sides.

        All files of a spec are high priority when any of them changed (the Review API
        compares the whole spec), and context otherwise.
        """
        closures: dict[tuple[str, str], set[str]] = {}  # (side, spec) -> files
        for side in SIDES:
            for spec in self.spec_roots(side):
                closures[(side, spec)] = self.ref_closure(spec, side)
        by_spec: dict[str, set[str]] = defaultdict(set)
        on_side: dict[str, set[str]] = defaultdict(set)  # path -> sides that need it
        for (side, spec), files in closures.items():
            by_spec[spec] |= files
            for path in files:
                on_side[path].add(side)
        changed: set[str] = set()
        for files in by_spec.values():
            if any(self.differs(path) for path in files):
                changed |= files
        units = []
        for path in sorted(on_side):
            unit = self.bundle_unit(
                "openapi",
                path,
                sorted(on_side[path]),
                changed=path in changed,
                record=self.differs(path),
            )
            if unit is not None:
                units.append(unit)
        return units

    def spec_roots(self, side: str) -> list[str]:
        tree = self.trees[side]
        roots: set[str] = set()
        for spec in self.config.openapi:
            path = normalize(spec)
            if path is None:
                self.skip(spec, "OpenAPI spec outside the repository")
            elif any(char in path for char in "*?["):
                regex = glob_regex(path)
                roots |= {p for p in tree if regex.fullmatch(p)}
            elif path in tree:
                roots.add(path)
        return sorted(roots)

    def ref_closure(self, spec: str, side: str) -> set[str]:
        tree = self.trees[side]
        seen: set[str] = set()
        todo = [spec]
        while todo and len(seen) < MAX_BUNDLE_FILES:
            path = todo.pop()
            entry = tree.get(path)
            if path in seen or entry is None or is_terraform(path):
                continue
            if not self.allowed(path, entry, record=self.differs(path)):
                continue
            seen.add(path)
            if not path.lower().endswith((".yaml", ".yml", ".json")):
                continue
            folder = posixpath.dirname(path)
            for target in ref_targets(self.text(entry)):
                resolved = normalize(posixpath.join(folder, target))
                if resolved is not None:
                    todo.append(resolved)
                elif self.differs(path):
                    self.skip(
                        posixpath.join(folder, target),
                        f"OpenAPI $ref outside the repository (from {display(path)})",
                    )
        return seen

    def event_units(self) -> list[Unit]:
        """Every file that matches repo-config kafka_schema_paths, on both sides."""
        if not self.config.schemas:
            return []
        on_side: dict[str, set[str]] = defaultdict(set)
        for side in SIDES:
            matches = sorted(p for p in self.trees[side] if self.config.schemas.match(p))
            for path in matches[MAX_BUNDLE_FILES:]:
                if self.differs(path):
                    self.skip(path, f"more than {MAX_BUNDLE_FILES} event schema files ({side})")
            for path in matches[:MAX_BUNDLE_FILES]:
                on_side[path].add(side)
        units = []
        for path in sorted(on_side):
            changed = self.differs(path)
            unit = self.bundle_unit(
                "events", path, sorted(on_side[path]), changed=changed, record=changed
            )
            if unit is not None:
                units.append(unit)
        return units

    def knowledge_units(self, changes: list[Change]) -> list[Unit]:
        """Changed files that match repo-config knowledge_paths, on both sides."""
        if not self.config.knowledge:
            return []
        units = []
        for change in changes:
            members = []
            for side, path in self.sides(change):
                entry = self.trees[side].get(path)
                if (
                    entry is None
                    or not self.config.knowledge.match(path)
                    or is_terraform(path)
                    or not self.allowed(path, entry)
                ):
                    continue
                name = f"bundles/knowledge/{side}/{path}"
                members.append(Member(name, entry.size, oid=entry.oid))
            if members:
                units.append(
                    Unit(
                        key=("knowledge", change.path),
                        priority=BUNDLE,
                        reason="over the archive size limit (knowledge bundle)",
                        paths=[change.path],
                        members=members,
                    )
                )
        return units

    def request_document(self, changes: list[Change], skipped: list[dict[str, str]]) -> bytes:
        """request.json: the ReviewRequest model of xrepo_core.payloads."""
        document = {
            "request_id": self.request_id,
            "repo": self.repo,
            "pr": {
                "number": self.pr.number,
                "base_sha": self.base_sha,
                "head_sha": self.head_sha,
                "merge_base_sha": self.merge_base_sha,
                "links": parse_links(self.pr.body, self.repo, self.pr.number),
            },
            "skipped": skipped,
            "config_version": self.config.config_version,
            "dry_run": False,
            "force": self.force,
            "changed_files": [
                {
                    "path": display(c.path),
                    "status": c.status,
                    "previous_path": display(c.previous_path) if c.previous_path else None,
                }
                for c in changes
            ],
        }
        text = json.dumps(document, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        return (text + "\n").encode("utf-8")

    def skipped_entries(self, extra: Iterable[tuple[str, str]] = ()) -> list[dict[str, str]]:
        return [{"path": p, "reason": r} for p, r in sorted(self.skipped | set(extra))]

    def build(self) -> BuildResult:
        self.resolve_commits()
        self.request_id = f"{self.repo}#{self.pr.number}@{self.head_sha}"
        self.trees = {
            "base": self.git.tree(self.merge_base_sha),
            "head": self.git.tree(self.head_sha),
        }
        changes = self.git.changes(self.merge_base_sha, self.head_sha)
        infra = self.build_infra(changes)

        units, diff_groups = self.file_units(changes)
        units += self.openapi_units()
        units += self.event_units()
        units += self.knowledge_units(changes)

        limit = self.config.max_archive_bytes
        diff = b""
        if diff_groups:
            diff = self.git.diff(self.merge_base_sha, self.head_sha, diff_groups)
        diff = cut_diff(diff, min(DIFF_LIMIT_BYTES, max(limit // 4, 4096)))
        # Reserve room for the largest possible request.json: every unit listed in skipped.
        drops = [(display(path), unit.reason) for unit in units for path in unit.paths]
        largest_request = self.request_document(changes, self.skipped_entries(drops))
        budget = (
            tar_budget(limit)
            - tar_member_size("request.json", len(largest_request))
            - tar_member_size("diff.patch", len(diff))
        )
        if budget < 0:
            raise PayloadError(
                f"limits.max_archive_bytes ({limit}) is too small for request.json and diff.patch"
            )
        kept: list[Unit] = []
        used = count = 0
        for unit in sorted(units, key=lambda u: (-u.priority, u.size, u.key)):
            if used + unit.size <= budget and count + len(unit.members) <= MAX_MEMBERS - 2:
                kept.append(unit)
                used += unit.size
                count += len(unit.members)
            else:
                for path in unit.paths:
                    self.skip(path, unit.reason)

        skipped = self.skipped_entries()
        request = self.request_document(changes, skipped)
        members = [member for unit in kept for member in unit.members]
        members.append(Member("diff.patch", len(diff), data=diff))
        members.append(Member("request.json", len(request), data=request))
        archive = self.out_dir / "request.tar.gz"
        size = write_archive(archive, members, self.read_member)
        if size > limit:
            raise PayloadError(f"request.tar.gz has {size} bytes, over the limit of {limit}")
        request_json = self.out_dir / "request.json"
        request_json.write_bytes(request)
        files = sum(1 for member in members if member.name.startswith("files/"))
        print(f"request.tar.gz: {len(members)} members ({files} changed files), {size} bytes")
        for item in skipped[:200]:
            print(f"skipped: {log_text(item['path'])}: {item['reason']}")
        if len(skipped) > 200:
            print(f"skipped: {len(skipped) - 200} more (see request.json)")
        return BuildResult(archive, request_json, infra, self.request_id, files, skipped)

    def cleanup(self) -> None:
        for folder in self.temp_dirs:
            shutil.rmtree(folder, ignore_errors=True)


def _module_members(work: Path, root: str, side: str) -> Iterator[Member]:
    """Files that terraform get downloaded, without links, .git folders, or secret files."""
    top = work / root / ".terraform" / "modules"
    for folder, subfolders, names in os.walk(top):
        subfolders[:] = sorted(
            d for d in subfolders if d != ".git" and not os.path.islink(os.path.join(folder, d))
        )
        for name in sorted(names):
            full = os.path.join(folder, name)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            relative = Path(full).relative_to(work).as_posix()
            if name_problem(relative) is None and not is_secret(relative):
                yield Member(f"infra/{side}/{relative}", os.path.getsize(full), file=full)


def _size(members: Iterable[Member]) -> int:
    return sum(tar_member_size(m.name, m.size) for m in members)


def _temp_root() -> str | None:
    return os.environ.get("RUNNER_TEMP") or None


# ---------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------


def parse_args(argv: list[str] | None, environ: Mapping[str, str]) -> argparse.Namespace:
    runner_temp = environ.get("RUNNER_TEMP")
    default_out = os.path.join(runner_temp, "xrepo", "payload") if runner_temp else None
    parser = argparse.ArgumentParser(description="Pack one pull request for the xrepo Review API.")
    parser.add_argument(
        "--config", default=environ.get("XREPO_CONFIG"), help="repo-config JSON (XREPO_CONFIG)"
    )
    parser.add_argument("--pr", default=environ.get("XREPO_PR"), help="pr.json (XREPO_PR)")
    parser.add_argument(
        "--force", default=environ.get("XREPO_FORCE", "false"), help='"true" for /xrepo recheck'
    )
    parser.add_argument(
        "--output-dir",
        default=environ.get("XREPO_OUTPUT_DIR") or default_out,
        help="folder for the archives (XREPO_OUTPUT_DIR, default $RUNNER_TEMP/xrepo/payload)",
    )
    parser.add_argument(
        "--repo-path",
        default=environ.get("XREPO_REPO_PATH") or ".",
        help="checked-out repository (XREPO_REPO_PATH)",
    )
    parser.add_argument(
        "--repository",
        default=environ.get("XREPO_REPOSITORY") or environ.get("GITHUB_REPOSITORY"),
        help="owner/name (XREPO_REPOSITORY, default GITHUB_REPOSITORY)",
    )
    return parser.parse_args(argv)


def set_outputs(values: Mapping[str, str], path: str | None) -> None:
    """Append step outputs to $GITHUB_OUTPUT (or print them when it is not set)."""
    lines = []
    for key, value in values.items():
        if "\n" in value or "\r" in value:
            raise PayloadError(f"output {key} contains a line break")
        lines.append(f"{key}={value}\n")
    if path:
        with open(path, "a", encoding="utf-8") as handle:
            handle.writelines(lines)
    else:
        sys.stdout.writelines(lines)


def _escape(text: str) -> str:
    return text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def run(options: argparse.Namespace) -> BuildResult:
    if not options.repository or not _REPO.fullmatch(options.repository):
        raise PayloadError("repository must look like owner/name (set GITHUB_REPOSITORY)")
    if not options.output_dir:
        raise PayloadError("no output folder: set --output-dir or RUNNER_TEMP")
    repo_path = Path(options.repo_path).resolve()
    if not repo_path.is_dir():
        raise PayloadError(f"repository folder not found: {repo_path}")
    config = read_config(options.config)
    pr = read_pr(options.pr)
    out_dir = Path(options.output_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    for stale in ("request.tar.gz", "request.json", "infra.tar.gz"):
        (out_dir / stale).unlink(missing_ok=True)
    force = str(options.force).strip().lower() == "true"
    git = Git(repo_path)
    builder = Builder(git, config, pr, options.repository, force, out_dir)
    try:
        return builder.build()
    finally:
        git.close()
        builder.cleanup()


def main(argv: list[str] | None = None) -> int:
    try:
        result = run(parse_args(argv, os.environ))
        set_outputs(
            {
                "request": str(result.request),
                "request_json": str(result.request_json),
                "infra": str(result.infra) if result.infra else "",
                "has_infra": "true" if result.infra else "false",
                "request_id": result.request_id,
                "files": str(result.files),
                "skipped": str(len(result.skipped)),
            },
            os.environ.get("GITHUB_OUTPUT"),
        )
    except PayloadError as exc:
        print(f"::error title=xrepo build-payload::{_escape(str(exc))}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
