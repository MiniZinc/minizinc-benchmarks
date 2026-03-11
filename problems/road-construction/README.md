# Road Construction (naive MiniZinc model)

## What problem is this model solving?

This model chooses which roads to build between `n` locations (cities/nodes), subject to a **budget limit**.

- Each possible road `(x,y)` has:
  - a construction `cost[x,y]`
  - a travel `distance[x,y]` if that road is built
- If a road is **not** built, travel through that direct edge is treated as very large (using a big constant `M`), so it is effectively unavailable.

The goal is to build a network of roads that stays within budget and gives good overall connectivity.

## Main decision variables

- `construct[x,y] : var bool`
  - `true` if road `(x,y)` is built, `false` otherwise.
  - The model enforces symmetry: `construct[y,x] = construct[x,y]`.
  - No self-road is allowed: `construct[x,x] = false`.

- `sp[x,y,s] : var 0..M`
  - An auxiliary variable used to represent shortest-path estimates from `x` to `y` after `s` relaxation steps.
  - Think of `s` as “how many rounds of path improvement have been applied.”

- `objective : var ...`
  - The total sum of final shortest-path distances between all unordered pairs `(x,y)` with `x < y`.

## Constraints in plain language

1. **Initialization**
   - Distance from a node to itself is always 0 (`sp[x,x,s] = 0`).
   - For each direct edge `(x,y)`, initial shortest-path value is:
     - `distance[x,y]` if built
     - `M` if not built

2. **Undirected network consistency**
   - If the network is undirected, both `construct` and shortest-path tables are mirrored across `(x,y)` and `(y,x)`.

3. **Shortest-path propagation**
   - For each step `s+1`, `sp[x,y,s+1]` is the minimum of:
     - previous value `sp[x,y,s]`
     - paths going through an intermediate node `z`
   - This is a dynamic-programming style relaxation similar to all-pairs shortest-path updates.

4. **Budget limit**
   - Total construction cost of selected roads must be `<= budget`.

5. **Objective definition**
   - `objective` equals the sum of final pairwise shortest-path values `sp[x,y,n]` for all `x < y`.

## Objective

The model **minimizes**:

- total pairwise shortest-path distance across the built network,
- while respecting the budget.

So the solver tries to spend the budget on roads that make travel between all node pairs as short as possible overall.

## Notes on uncertainty / assumptions

- This file is named `road_naive.mzn`; it appears to be a straightforward formulation emphasizing clarity over advanced optimization.
- The model assumes data are consistent for an undirected graph (for example, matching symmetric entries where needed).
- `M = 1000000` is a standard “big-M” penalty choice; if too small for a dataset, it could accidentally allow undesirable paths, and if too large, it can weaken propagation/performance.
- The exact real-world interpretation (cities, settlements, logistics hubs, etc.) is not specified in this file alone.

## Identifiable references

- Author line in source comment: **Rehan Abdul Aziz** (`raziz@student.unimelb.edu.au`).
- Methodology resemblance: iterative shortest-path relaxation (conceptually related to all-pairs shortest-path dynamic programming, e.g., Floyd–Warshall-style updates).
