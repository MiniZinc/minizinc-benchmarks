# Tiny CVRP (Exactly One Solution) — Beginner-Friendly Model Guide

## What problem is this model trying to solve?
This MiniZinc model represents a small **Capacitated Vehicle Routing Problem (CVRP)**.

In plain words:
- There is one depot (location `1`) and several customer locations (`2..total_places`).
- A fixed number of vehicles must serve all customers.
- Each customer must be assigned to exactly one vehicle.
- Each vehicle has a capacity limit, so it cannot carry more demand than allowed.
- The model tries to minimize a total travel-time-like cost (`total_ETA`) based on a matrix of predicted ETAs.

---

## Main inputs (data)
The model expects these parameters from a `.dzn` file or equivalent data source:

- `num_vehicles`: number of vehicles.
- `num_customers`: number of customers.
- `predicted_ETAs[i,j]`: travel estimate between places `i` and `j` (including depot).
- `vehicle_capacities[v]`: capacity of each vehicle.
- `predicted_demands[c]`: demand at each place.

Derived value:
- `total_places = num_customers + 1` (customer places plus depot).

---

## Decision variables
The model decides:

- `visit[v,c]` (0/1): whether vehicle `v` visits place `c`.
- `order[v,c]`: sequence index used to represent visit order for each vehicle.
  - `order[v,1] = 1` forces the depot to be first.
  - `order[v,total_places+1]` is used as an extra slot to represent return-to-depot timing.

And computes:
- `total_ETA`: total route cost used in the objective.

---

## Core constraints (high level)
1. **Vehicle capacity**
   - For each vehicle, sum of assigned demands cannot exceed that vehicle’s capacity.

2. **Each customer visited exactly once**
   - Every customer (`2..total_places`) must be visited by exactly one vehicle.

3. **Depot start**
   - Every vehicle must include the depot and start there in order position `1`.

4. **Visit ordering**
   - If a customer is visited by a vehicle, its `order` must be greater than earlier visited places (as encoded by index-based logic).
   - If not visited, its `order` is forced to `0`.

5. **Return to depot encoding**
   - The model computes a vehicle-specific “last customer order” and sets the extra order position (`total_places+1`) to one step after that.

---

## Objective
Yes, this model has an objective:

- **Minimize `total_ETA`**.

So it searches for a feasible assignment/ordering with lowest computed ETA cost.

---

## Important modeling notes and uncertainty
This file is clearly intended as CVRP-style logic, but some details are non-standard and may not match textbook routing formulations exactly:

- The ETA accumulation uses pairwise combinations of visited nodes (`i < j`) rather than explicit arc-by-arc route transitions.
- “Last customer” in `total_ETA` is computed from the **largest customer index visited**, not necessarily the final stop in the route order.
- The ordering rule depends on customer index progression (`k in 1..c-1`) and does not explicitly define predecessor/successor arcs.
- The model includes a specific search annotation (`int_search(...)`), but this guide intentionally focuses on modeling semantics rather than search strategy.

Because of these choices, treat the model as a compact/experimental CVRP variant rather than a canonical full VRP formulation.

---

## References (identifiable from the file)
- Problem family: **Capacitated Vehicle Routing Problem (CVRP)** (standard OR/CP routing problem class).
- License header in the model: **MIT License**.

No explicit paper citation, benchmark source URL, or original author metadata is embedded directly in this `.mzn` file.

## Model update summary

Added concise inline comments in TinyCVRP_ExactlyOneSolution.mzn to clarify:

- vehicle-visit and order decision variable semantics,
- capacity and visit-uniqueness feasibility constraints,
- objective intent as minimizing total ETA cost.
