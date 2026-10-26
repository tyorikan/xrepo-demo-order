package com.example.order;

import java.util.List;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.constraints.NotNull;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.http.ResponseEntity;
import org.springframework.kafka.annotation.KafkaListener;
import org.springframework.kafka.core.KafkaTemplate;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.client.RestTemplate;

@RestController
@RequestMapping("/v1/orders")
public class OrderController {

    @Value("${CATALOG_SERVICE_URL}")
    private String catalogServiceUrl;

    private final RestTemplate restTemplate;
    private final KafkaTemplate<String, OrderCreatedEvent> kafkaTemplate;

    public OrderController(
        RestTemplate restTemplate,
        KafkaTemplate<String, OrderCreatedEvent> kafkaTemplate
    ) {
        this.restTemplate = restTemplate;
        this.kafkaTemplate = kafkaTemplate;
    }

    @PostMapping("/{id}/confirm")
    public ResponseEntity<OrderResponse> confirmOrder(@PathVariable("id") String id) {
        CatalogItemResponse catalog = restTemplate.getForObject(
            catalogServiceUrl + "/v1/items/" + id, CatalogItemResponse.class
        );
        long totalYen = 0L;
        for (CatalogOfferDto offer : catalog.getItems()) {
            totalYen += (long) offer.getPrice();
        }
        OrderCreatedEvent evt = new OrderCreatedEvent(id, "res-" + id, totalYen, "CREATED");
        kafkaTemplate.send("${app.kafka.order-topic}", id, evt);
        return ResponseEntity.ok(new OrderResponse(id, totalYen));
    }

    @GetMapping("/healthz")
    public String health() {
        return "ok";
    }

    @KafkaListener(topics = "${app.kafka.order-topic}")
    public void onOrderCreatedAudit(OrderCreatedEvent event) {
        try {
            String reservationId = event.getReservationId();
            long totalYen = event.getTotalYen();
            if (reservationId.isEmpty() || totalYen < 0) {
                throw new IllegalStateException("Invalid order event");
            }
        } catch (Exception ex) {
            sendToDlq(event);
        }
    }

    private void sendToDlq(OrderCreatedEvent event) {}
}

class CatalogOfferDto {
    private int price;
    private String currency;
    public int getPrice() { return price; }
    public String getCurrency() { return currency; }
}

class CatalogItemResponse {
    private String id;
    private List<CatalogOfferDto> items;
    public String getId() { return id; }
    public List<CatalogOfferDto> getItems() { return items; }
}

class OrderResponse {
    @NotNull
    private String orderId;
    private long totalYen;
    public OrderResponse(String orderId, long totalYen) {
        this.orderId = orderId;
        this.totalYen = totalYen;
    }
}

class OrderCreatedEvent {
    @NotNull
    private String orderId;
    @NotNull
    private String reservationId;
    private long totalYen;
    private String status;

    public OrderCreatedEvent(String orderId, String reservationId, long totalYen, String status) {
        this.orderId = orderId;
        this.reservationId = reservationId;
        this.totalYen = totalYen;
        this.status = status;
    }

    public String getReservationId() { return reservationId; }
    public long getTotalYen() { return totalYen; }
    public String getStatus() { return status; }
}
