# CVRPTW with Reloads (MiniZinc model overview)

This model, `cvrptw_w_reload.mzn`, encodes a **vehicle routing problem** with several practical features:

- **Capacitated vehicles** (each vehicle has a load limit)
- **Time windows** (customers must be visited within allowed time intervals)
- **Pickup-and-delivery pairing** (linked requests must be handled by the same vehicle, with precedence)
- **Depot start/end nodes per vehicle** (route representation uses explicit start and end depot nodes)

In short: the solver must build feasible routes for multiple vehicles so all customers are served while respecting time and capacity rules, then minimize total route time.

## What data the model expects

The model is parameterized by:

- `M`: number of customer nodes
- `K`: number of vehicles
- `Demand[1..M]`: load change at each customer
- `TravelTime[1..N,1..N]`: travel times between all nodes
- `TimeWindows[1..M,1..2]`: earliest/latest arrival for each customer
- `PDs[1..M,1..2]`: pickup-delivery linkage indices
- `Capacity[1..K]`: vehicle capacities

It builds an expanded node set `N = M + 2K`, where the extra `2K` nodes are start/end depots (one pair per vehicle).

## Decision variables (beginner view)

Key variables are:

- `successor[n]`: the next node visited after node `n`
- `predecessor[n]`: the previous node before `n` (redundant but useful for propagation)
- `vehicle[n]`: which vehicle serves node `n`
- `arrivalTime[n]`: arrival time at node `n`
- `slack[n]`: waiting/slack time before moving to the successor
- `load[n]`: vehicle load state along the route
- `objective`: scalar cost to minimize

These variables describe full vehicle tours and their timing/load evolution.

## Main constraints

The model enforces:

1. **Single tour structure over all nodes** via `circuit(successor)` (with depot wiring constraints to stitch per-vehicle routes into one circuit representation).
2. **Consistency of predecessor/successor** and vehicle assignment across linked nodes.
3. **Pickup-delivery coupling**:
   - pickup and delivery must use the same vehicle,
   - precedence in time (`arrivalTime` ordering) is imposed.
4. **Time propagation**:
   - `arrivalTime[n] + slack[n] + TravelTime[n, successor[n]] = arrivalTime[successor[n]]`
5. **Time windows** at customer nodes.
6. **Capacity/load flow** and per-vehicle capacity limits.

## Objective

The model minimizes:

- Sum of arrival times at end depots
- minus sum of arrival times at start depots

This acts as a proxy for total route duration/travel time across vehicles.

## Notes and uncertainty

- The filename says “with reload”, but in this specific model text there is no explicit standalone reload-node mechanism beyond depot-node modeling; reload behavior may be implicit in data conventions or in a related variant.
- The exact semantics of `PDs[i,1]` vs `PDs[i,2]` are not fully documented inside this file; constraints use `PDs[n,2]` directly.
- `Demand` sign convention (positive delivery vs pickup) is instance-dependent and not explicitly explained in-model.

## Identifiable references

From model comments:

- CP formulation inspired by **Andrea Rendl (2015)** work on VRP-style modeling.
- Routing ideas adapted from the **Google OR-Tools LNS routing model**.
- Model adaptation/copyright notice names **Haakon H. Rød (2021)** under an MIT-style permission notice.

If you want, I can also generate a small “how to run” section using one of the instance files in `data/` and show expected MiniZinc CLI commands.
