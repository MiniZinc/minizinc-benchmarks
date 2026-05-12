# VRPLC Service Model (`vrplc_service.mzn`)

This MiniZinc model encodes the **Vehicle Routing Problem with Location Congestion (VRPLC)**, which combines:
- a pickup-and-delivery routing problem with time windows, and
- a scheduling limit on how many requests can be serviced at the same location at once.

In simple terms: several identical vehicles leave a depot, perform pickup and delivery jobs within allowed time windows, respect vehicle load capacity, and avoid overloading location service capacity.

## What problem is being solved?

The model builds feasible routes for `V` vehicles over `P` pickup-delivery pairs (`R = 2*P` request nodes), with start/end depot nodes added per vehicle. It must satisfy:
- **Routing consistency** (every node has one successor, no subtours),
- **Time consistency** (travel + service timing and time windows),
- **Load consistency** (vehicle capacity over the route),
- **Pickup-before-delivery and same-vehicle pairing**,
- **Location congestion limits** via `cumulative`.

## Main decision variables

- `succ[i]`: the next node visited after node `i` (route structure).
- `veh[i]`: which vehicle serves node `i`.
- `arr[i]`: arrival time at node `i`.
- `ser[i]`: service start time at node `i`.
- `dep[i]`: departure time from node `i`.
- `load[i]`: load after visiting node `i`.
- `objective`: total travel-time cost expression value.

## Constraint groups (beginner view)

1. **Route construction**
   - `circuit(succ)` enforces a single permutation-style successor structure.
   - Additional constraints connect vehicle start/end nodes into a giant-tour representation.
   - Symmetry breaking reduces equivalent mirrored solutions.

2. **Time constraints**
   - Arrival ≤ service start ≤ time-window end.
   - Service duration is respected (`ser + s <= dep`).
   - Travel-time propagation: departure at `i` + travel to `succ[i]` = arrival at successor.

3. **Load constraints**
   - Load propagates along arcs using request load changes `q`.
   - Start/end depot-type nodes are forced to zero load.

4. **Pickup-delivery logic**
   - Delivery node for request `i` happens after its pickup.
   - Pickup and its matching delivery must be on the same vehicle.

5. **Location congestion (`cumulative`)**
   - For each location `ll`, all services occurring there consume unit resource during their service interval.
   - Total simultaneous services cannot exceed location capacity `C`.

## Objective

The model **minimizes total travel time**:

\[
\text{objective} = \sum_{i \in \text{RSNODES}} time[i, succ[i]]
\]

So it seeks the lowest route travel-time cost while satisfying all routing, timing, capacity, and congestion constraints.

## Solve/search note

The model includes an explicit search annotation (`seq_search(...)`) over `succ`, then timing variables, load, and vehicle variables. This affects solver guidance but is not part of the mathematical problem definition.

## Uncertainty and assumptions

- This description is inferred from the model file alone; exact real-world semantics of some node subsets (`RSNODES`, `SENODES`) depend on instance-generation conventions.
- The objective uses arc travel times only; if data includes waiting penalties or other costs, they are not represented here.
- The comments and structure suggest a standard single-depot, identical-vehicle setting, but depot interpretation is encoded indirectly through synthetic start/end nodes.

## Reference

Identifiable source from model header:
- Edward Lam, Pascal Van Hentenryck (2016), *A branch-and-price-and-check model for the vehicle routing problem with location congestion*, **Constraints** 21(3): 394–412.
- Link noted in source comments: https://link.springer.com/article/10.1007/s10601-016-9241-2

## Model update summary

Added concise inline comments in vrplc_service.mzn to clarify:

- route, timing, and load decision variable semantics,
- pickup/delivery and congestion feasibility constraints,
- objective intent as minimizing total route travel time.
