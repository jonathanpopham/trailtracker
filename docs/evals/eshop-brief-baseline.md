# Codebase brief: /private/tmp/claude-501/-Users-jag/e05fd682-3a3e-4c4f-8cb7-f66d17e5c3ac/scratchpad/eShop

## Overview

- 4130 nodes, 9775 edges — 540 file(s), 26166 line(s)

### Languages

- csharp — 527 file(s), 25908 line(s), 3297 node(s)
- javascript — 6 file(s), 31 line(s), 19 node(s)
- powershell — 2 file(s), 60 line(s), 5 node(s)
- typescript — 5 file(s), 167 line(s), 12 node(s)

## Architecture

### Largest units (by contained symbols)

- `src/ClientApp/Services/Basket/Protos/Basket.cs` (File) — 132 symbol(s)
- `tests/ClientApp.UnitTests/Mocks/MockSettingsService.cs` (File) — 52 symbol(s)
- `src/ClientApp/ViewModels/SettingsViewModel.cs` (File) — 50 symbol(s)
- `src/ClientApp/Services/Settings/SettingsService.cs` (File) — 39 symbol(s)
- `src/ClientApp/Services/Basket/Protos/BasketGrpc.cs` (File) — 33 symbol(s)
- `tests/Ordering.UnitTests/Domain/SeedWork/ValueObjectTests.cs` (File) — 27 symbol(s)
- `src/ClientApp/ViewModels/CatalogViewModel.cs` (File) — 26 symbol(s)
- `src/Ordering.Domain/AggregatesModel/OrderAggregate/Order.cs` (File) — 25 symbol(s)
- `tests/Basket.UnitTests/Helpers/TestServerCallContext.cs` (File) — 24 symbol(s)
- `src/Ordering.API/Application/Queries/OrderViewModel.cs` (File) — 22 symbol(s)

### Module dependency map (cross-file references)

- src/ClientApp/Services/Basket/Protos/BasketGrpc.cs -> src/ClientApp/Services/Basket/Protos/Basket.cs — 35 reference(s)
- src/Catalog.API/Apis/CatalogApi.cs -> src/Catalog.API/Model/CatalogServices.cs — 13 reference(s)
- tests/ClientApp.UnitTests/ViewModels/CatalogViewModelTests.cs -> src/ClientApp/ViewModels/CatalogViewModel.cs — 13 reference(s)
- src/Basket.API/Grpc/BasketService.cs -> src/ClientApp/Services/Basket/Protos/Basket.cs — 8 reference(s)
- src/Catalog.API/Apis/CatalogApi.cs -> src/Catalog.API/Model/PaginatedItems.cs — 7 reference(s)
- src/Catalog.API/Apis/CatalogApi.cs -> src/Catalog.API/Model/PaginationRequest.cs — 7 reference(s)
- src/Ordering.Domain/AggregatesModel/OrderAggregate/Order.cs -> src/Ordering.Domain/SeedWork/Entity.cs — 7 reference(s)
- tests/ClientApp.UnitTests/ViewModels/MockViewModelTests.cs -> tests/ClientApp.UnitTests/Mocks/MockViewModel.cs — 6 reference(s)
- src/ClientApp/Animations/StoryBoard.cs -> src/ClientApp/Animations/Base/AnimationBase.cs — 5 reference(s)
- src/ClientApp/Services/Catalog/CatalogService.cs -> src/ClientApp/Helpers/UriHelper.cs — 5 reference(s)
- src/Ordering.Domain/AggregatesModel/BuyerAggregate/IBuyerRepository.cs -> src/Ordering.Domain/AggregatesModel/BuyerAggregate/Buyer.cs — 5 reference(s)
- src/eShop.ServiceDefaults/OpenApi.Extensions.cs -> src/eShop.ServiceDefaults/OpenApiOptionsExtensions.cs — 5 reference(s)
- tests/Ordering.UnitTests/Domain/SeedWork/ValueObjectTests.cs -> src/Ordering.Domain/SeedWork/ValueObject.cs — 5 reference(s)
- src/ClientApp/Services/AppEnvironment/AppEnvironmentService.cs -> src/ClientApp/Services/Basket/IBasketService.cs — 4 reference(s)
- src/ClientApp/Services/AppEnvironment/AppEnvironmentService.cs -> src/ClientApp/Services/Order/IOrderService.cs — 4 reference(s)
- src/ClientApp/Services/Basket/BasketService.cs -> src/ClientApp/Services/Basket/Protos/BasketGrpc.cs — 4 reference(s)
- src/ClientApp/ViewModels/CatalogViewModel.cs -> src/ClientApp/ViewModels/Base/ViewModelBase.cs — 4 reference(s)
- src/Identity.API/Quickstart/Consent/ConsentController.cs -> src/Identity.API/Quickstart/Consent/ConsentInputModel.cs — 4 reference(s)
- src/Identity.API/Quickstart/Device/DeviceController.cs -> src/Identity.API/Quickstart/Device/DeviceAuthorizationInputModel.cs — 4 reference(s)
- src/Ordering.API/Application/Behaviors/TransactionBehavior.cs -> src/Ordering.Infrastructure/OrderingContext.cs — 4 reference(s)
- … and 535 more cross-file link(s)

## Entry points

### Likely mains

_none detected — likely a library_

### Public API surface (referenced from outside their file)

- `IntegrationEvent` (Type, src/EventBus/Events/IntegrationEvent.cs) — 36 external reference(s)
- `IOrderRepository` (Type, src/Ordering.Domain/AggregatesModel/OrderAggregate/IOrderRepository.cs) — 28 external reference(s)
- `ISettingsService` (Type, src/ClientApp/Services/Settings/ISettingsService.cs) — 28 external reference(s)
- `INavigationService` (Type, src/ClientApp/Services/Navigation/INavigationService.cs) — 25 external reference(s)
- `IAppEnvironmentService` (Type, src/ClientApp/Services/AppEnvironment/IAppEnvironmentService.cs) — 24 external reference(s)
- `OrderStatus` (Type, src/Ordering.Domain/AggregatesModel/OrderAggregate/OrderStatus.cs) — 23 external reference(s)
- `Buyer` (Type, src/Ordering.Domain/AggregatesModel/BuyerAggregate/Buyer.cs) — 20 external reference(s)
- `IOrderingIntegrationEventService` (Type, src/Ordering.API/Application/IntegrationEvents/IOrderingIntegrationEventService.cs) — 18 external reference(s)
- `IdentifiedCommandHandler` (Type, src/Ordering.API/Application/Commands/IdentifiedCommandHandler.cs) — 15 external reference(s)
- `CustomerBasketResponse` (Type, src/ClientApp/Services/Basket/Protos/Basket.cs) — 15 external reference(s)

## Hotspots

### Highest fan-in (most depended upon — change ripples)

- `IntegrationEvent` (Type, src/EventBus/Events/IntegrationEvent.cs) — fan-in 37
- `IOrderRepository` (Type, src/Ordering.Domain/AggregatesModel/OrderAggregate/IOrderRepository.cs) — fan-in 28
- `ISettingsService` (Type, src/ClientApp/Services/Settings/ISettingsService.cs) — fan-in 28
- `INavigationService` (Type, src/ClientApp/Services/Navigation/INavigationService.cs) — fan-in 25
- `IAppEnvironmentService` (Type, src/ClientApp/Services/AppEnvironment/IAppEnvironmentService.cs) — fan-in 24
- `OrderStatus` (Type, src/Ordering.Domain/AggregatesModel/OrderAggregate/OrderStatus.cs) — fan-in 23
- `CustomerBasketResponse` (Type, src/ClientApp/Services/Basket/Protos/Basket.cs) — fan-in 22
- `Buyer` (Type, src/Ordering.Domain/AggregatesModel/BuyerAggregate/Buyer.cs) — fan-in 22
- `IOrderingIntegrationEventService` (Type, src/Ordering.API/Application/IntegrationEvents/IOrderingIntegrationEventService.cs) — fan-in 18
- `IdentifiedCommandHandler` (Type, src/Ordering.API/Application/Commands/IdentifiedCommandHandler.cs) — fan-in 17

### Highest fan-out (depends on the most — complexity)

- `BuildTargetModel` (Function, src/Ordering.Infrastructure/Migrations/20231021004633_FixOrderitemseqSchema.Designer.cs) — fan-out 23
- `BuildTargetModel` (Function, src/Ordering.Infrastructure/Migrations/20230925222426_Initial.Designer.cs) — fan-out 23
- `BuildModel` (Function, src/Ordering.Infrastructure/Migrations/OrderingContextModelSnapshot.cs) — fan-out 23
- `BuildTargetModel` (Function, src/Ordering.Infrastructure/Migrations/20231026091055_Outbox.Designer.cs) — fan-out 23
- `BuildTargetModel` (Function, src/Ordering.Infrastructure/Migrations/20240106121712_UseEnumForOrderStatus.Designer.cs) — fan-out 23
- `Callback` (Function, src/Identity.API/Quickstart/Account/ExternalController.cs) — fan-out 21
- `SeedAsync` (Function, src/Catalog.API/Infrastructure/CatalogContextSeed.cs) — fan-out 21
- `MapWebHooksApiV1` (Function, src/Webhooks.API/Apis/WebHooksApi.cs) — fan-out 20
- `BuildTargetModel` (Function, src/Catalog.API/Infrastructure/Migrations/20231009153249_Initial.Designer.cs) — fan-out 19
- `AddApplicationServices` (Function, src/Catalog.API/Extensions/Extensions.cs) — fan-out 18

## Dependency cycles

- cycle of 2 file(s): src/ClientApp/Animations/Base/AnimationBase.cs <-> src/ClientApp/Triggers/BeginAnimation.cs
- cycle of 2 file(s): src/ClientApp/ViewModels/Base/ViewModelBase.cs <-> src/ClientApp/ViewModels/SettingsViewModel.cs
- cycle of 3 file(s): src/Ordering.API/Application/Commands/CreateOrderDraftCommand.cs <-> src/Ordering.API/Application/Commands/CreateOrderDraftCommandHandler.cs <-> src/Ordering.API/Extensions/BasketItemExtensions.cs
- cycle of 2 file(s): src/Ordering.Domain/AggregatesModel/BuyerAggregate/Buyer.cs <-> src/Ordering.Domain/Events/BuyerPaymentMethodVerifiedDomainEvent.cs
- cycle of 2 file(s): src/Ordering.Infrastructure/MediatorExtension.cs <-> src/Ordering.Infrastructure/OrderingContext.cs

## What this repo is

This repo is a polyglot codebase (mostly csharp, 4 languages): 540 file(s), 26166 line(s), modeled as 4130 nodes and 9775 edges. Its largest unit is `src/ClientApp/Services/Basket/Protos/Basket.cs` (File) with 132 symbol(s). No `main` was detected, so it reads as a library whose public surface is led by `IntegrationEvent` (Type, src/EventBus/Events/IntegrationEvent.cs). The most depended-upon symbol is `IntegrationEvent` (Type, src/EventBus/Events/IntegrationEvent.cs) (fan-in 37) — changes there ripple widest; `BuildTargetModel` (Function, src/Ordering.Infrastructure/Migrations/20231021004633_FixOrderitemseqSchema.Designer.cs) carries the most outbound complexity (fan-out 23). Dependency cycles knot the file graph — see the cycles section before refactoring.
