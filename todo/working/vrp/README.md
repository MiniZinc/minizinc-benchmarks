# Vehicle Routing Problem (VRP) — MiniZinc Model Explainer

## What problem does this model solve?
This model encodes a **capacitated vehicle routing problem (CVRP)**:

- A depot sends out up to `K` vehicles.
- Each customer node must be visited exactly once.
- Each vehicle route must respect vehicle capacity.
- The goal is to minimize total travel distance.

In short: find a set of depot-start/depot-end tours that serve all customers at minimum distance, without overloading vehicles.

## Inputs (data parameters)
- `N`: number of non-depot nodes (customers in the constraints as written).
- `Capacity`: capacity of each vehicle.
- `K = N`: maximum number of vehicles (default is very loose; data may override).
- `Demand[1..N]`: demand per customer.
- `Distance[1..N+1, 1..N+1]`: distance/cost matrix.

The model uses internal node indices `0..N` for routing arcs, where node `0` is intended to be the depot.

## Decision variables
- `x[i,j] in {0,1}` for `i,j in 0..N`:
  - `1` means arc from node `i` to node `j` is used in the final routes.
  - `0` means it is not used.
- `u[i] in 0..Capacity` for `i in 1..N`:
  - helper load variables used by subtour-elimination/capacity constraints (MTZ-style).

## Core constraints (plain language)
1. **Each customer has exactly one incoming arc**  
   `sum_i x[i,j] = 1` for every customer `j`.

2. **Each customer has exactly one outgoing arc**  
   `sum_j x[i,j] = 1` for every customer `i`.

3. **Depot degree is limited by vehicle count**  
   - inbound to depot `<= K`
   - outbound from depot `<= K`

4. **Subtour elimination + capacity progression (MTZ form)**  
   `u[i] - u[j] + Capacity * x[i,j] <= Capacity - Demand[j]` and `Demand[i] <= u[i]`.  
   This ties route connectivity to load variables so disconnected customer-only cycles are prevented and capacity feasibility is enforced along routes.

## Objective
The model **minimizes total distance**:

\[
\text{objective} = \sum_{i=0}^{N}\sum_{j=0}^{N} Distance[i+1,j+1] \cdot x[i,j]
\]

(Offset `+1` appears because MiniZinc arrays are 1-based while route nodes are modeled as `0..N`.)

## What this model returns
The output prints:
- `x`: the selected arcs (route structure)
- `objective`: total travel cost

## Uncertainty / modeling notes
- The comment says “Node 0 corresponds to the depot,” but `Demand` is defined on `1..N`. This is consistent with “customers are `1..N`, depot is `0`,” though data files should confirm interpretation.
- `K` defaults to `N`, so unless overridden, the vehicle limit is weak.
- The model does not explicitly forbid self-loops (`x[i,i]`), so feasibility typically relies on distance data/other constraints making them unattractive or impossible.
- This README explains model intent from `vrp.mzn` only; exact benchmark semantics depend on the accompanying data files.

## References (identifiable)
- Miller, C. E., Tucker, A. W., & Zemlin, R. A. (1960). Integer programming formulation of traveling salesman problems. *Journal of the ACM*, 7(4), 326–329. (basis of MTZ-style subtour elimination)
- Standard CVRP formulation literature (depot/customer routing with capacity-constrained vehicles).
