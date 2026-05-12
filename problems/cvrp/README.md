# Capacitated Vehicle Routing Problem (CVRP)

## Problem Description

The **Capacitated Vehicle Routing Problem (CVRP)** is a classic combinatorial optimisation problem. The goal is to plan a set of delivery routes from a central **depot** to a collection of **customers**, using a fleet of vehicles, such that:

- Every customer is visited **exactly once**.
- No vehicle's total load exceeds its **capacity**.
- All vehicles start and finish at the depot.
- The total travel time (or distance) across all routes is **minimised**.

This model uses a _giant tour_ (or successor-chain) representation, where all routes are encoded as a single circuit that passes through special depot nodes separating one vehicle's route from the next.

## Parameters

| Parameter  | Description                                                                                                                       |
| ---------- | --------------------------------------------------------------------------------------------------------------------------------- |
| `N`        | Number of customers (also used as the maximum number of vehicles)                                                                 |
| `Capacity` | Maximum load any single vehicle can carry                                                                                         |
| `Demand`   | Array of integer demands, one per customer                                                                                        |
| `Distance` | An `(N+1) × (N+1)` matrix of travel distances/times between all locations; index `1` is the depot, indices `2..N+1` are customers |

## Node Representation

The model works with an extended set of **nodes**:

- Nodes `1..N` — the customers.
- Nodes `N+1..N+nbVehicles` — **start depot** nodes (one per vehicle entry into the tour).
- Nodes `N+nbVehicles+1..N+2*nbVehicles` — **end depot** nodes (one per vehicle exit from the tour).

Each vehicle has a dedicated start/end depot node pair. The end depot nodes are wired directly back to the corresponding start depot nodes, forming a closed circuit over all nodes.

## Decision Variables

| Variable      | Type / Domain                       | Meaning                                                                                                 |
| ------------- | ----------------------------------- | ------------------------------------------------------------------------------------------------------- |
| `successor`   | `array[NODES] of var NODES`         | For each node, which node the vehicle visits next                                                       |
| `predecessor` | `array[NODES] of var NODES`         | For each node, which node was visited immediately before it (redundant, used to strengthen propagation) |
| `vehicle`     | `array[NODES] of var VEHICLE`       | Which vehicle (1..N) is responsible for visiting each node                                              |
| `load`        | `array[NODES] of var 0..Capacity`   | Accumulated load on the vehicle upon **arriving** at a node                                             |
| `arrivalTime` | `array[NODES] of var 0..timeBudget` | Time at which the serving vehicle arrives at each node                                                  |
| `objective`   | `var 0..timeBudget`                 | Total travel time — the value to be minimised                                                           |

## Constraints

- **Circuit**: The `successor` array forms a single Hamiltonian circuit over all nodes (customers + depot start/end nodes), using the MiniZinc `circuit` global constraint. This implicitly ensures every customer is visited exactly once and eliminates sub-tours.
- **Vehicle propagation**: A customer inherits the same vehicle label as its predecessor, ensuring all nodes on a sub-tour belong to one vehicle.
- **Capacity**: The load accumulates along each route (`load[n] + demand[n] = load[successor[n]]`) and is bounded by `Capacity`. Vehicles start with zero load at their depot node.
- **Arrival time**: Times propagate forward along each route (`arrivalTime[n] + distance[n, successor[n]] ≤ arrivalTime[successor[n]]`). Vehicles depart the depot at time zero.
- **Depot structure**: End depot nodes connect directly back to their corresponding start depot nodes, and the vehicle assignments for depot nodes are fixed by their index.

## Objective

Minimise the **sum of arrival times at all end depot nodes**, which serves as a proxy for total travel time across all vehicle routes.

$$\text{minimise} \sum_{d \in \text{END\_DEPOT\_NODES}} \texttt{arrivalTime}[d]$$

## Notes

- The model was authored by **Andrea Rendl** (March 2015) and was adapted from instances originally designed for a MIP formulation of CVRP.
- The maximum number of vehicles equals the number of customers (`nbVehicles = N`), so in the worst case each customer is served by its own vehicle. In practice, optimal solutions will use far fewer.
- The `timeBudget` is computed as the sum of the maximum distance from each customer node, which provides a loose but valid upper bound on arrival times.

## References

- Dantzig, G. B., & Ramser, J. H. (1959). The Truck Dispatching Problem. _Management Science_, 6(1), 80–91. — The original formulation of the vehicle routing problem.
- Toth, P., & Vigo, D. (Eds.) (2002). _The Vehicle Routing Problem_. SIAM Monographs on Discrete Mathematics and Applications.
- Rendl, A., Guns, T., Stuckey, P. J., & Tack, G. (2015). Stochastic minizinc. _Proceedings of CP 2015_. — Likely context for this model's origin (note: attribution is approximate; please verify against the original source).

## Model update summary

Added concise inline comments in `cvrp.mzn` to clarify:

- the core routing variables (`successor`, `predecessor`, `vehicle`) and their roles in building routes,
- the capacity and timing tracking arrays (`load`, `arrivalTime`), and
- the objective function representing total travel time across all vehicle routes.
