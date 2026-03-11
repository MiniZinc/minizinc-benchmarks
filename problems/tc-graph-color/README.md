# Time-changing Graph Coloring (`tcgc2.mzn`)

## What problem is this model solving?
This MiniZinc model describes a **reconfiguration** version of graph coloring.

You are given:
- a graph (nodes and edges),
- an initial valid coloring of the nodes,
- a target valid coloring,
- a maximum number of time steps (`max_s`),
- and a limit `k` on how many nodes may change color between two consecutive steps.

The goal is to transform the initial coloring into the target coloring over time, while:
- keeping every intermediate coloring valid (adjacent nodes must have different colors), and
- changing at most `k` node colors per step.

---

## Main data and sets
- `nbV`, `nbE`: number of vertices and edges.
- `NODES = 1..nbV`, `EDGES = 1..nbE`.
- `heads[e]`, `tails[e]`: endpoints of edge `e`.
- `init[n]`: initial color of node `n`.
- `end[n]`: target color of node `n`.
- `c = max(init ++ end)`: number of colors available (derived from data).
- `COLORS = 1..c`.
- `max_s` (default 10): maximum modeled time horizon.
- `k`: max number of color changes allowed between consecutive steps.

---

## Decision variables
- `s` (integer in `2..max_s`): the time index at which the target coloring must be reached.
- `a[step,node]` in `COLORS`: color of each node at each step (`step = 1..max_s`).
- `objective`: scalar objective value used for minimization.

Interpretation:
- Row `a[1,*]` is fixed to `init`.
- Row `a[s,*]` is fixed to `end`.
- For steps after `s`, the model forces no further changes (state stays constant).

---

## Core constraints (beginner view)
1. **Start and end anchoring**
   - `a[1,n] = init[n]` for all nodes.
   - `a[s,n] = end[n]` for all nodes.

2. **Valid coloring at every step**
   - For each edge `(u,v)`, enforce `a[step,u] != a[step,v]`.

3. **Limited change per transition (before reaching `s`)**
   - If `i < s`, then number of nodes with `a[i,n] != a[i+1,n]` must be `<= k`.

4. **Freeze after reaching `s`**
   - If `i >= s`, enforce `a[i,n] = a[i+1,n]` for all nodes.

---

## Objective
The model minimizes:

- `objective = (k * max_s + 1) * s + total_number_of_changes_over_all_transitions`.

This creates a **lexicographic-like priority**:
1. Minimize `s` first (reach target as early as possible),
2. then, among equal `s`, minimize total color-change count.

Reason: the coefficient `(k * max_s + 1)` is larger than any possible total transition-change sum per unit change in `s`, so reducing `s` dominates.

---

## Notes and uncertainties
- `s` is restricted to `2..max_s`, so the model does **not** allow reaching the target at step 1. This is likely intentional, but not explicitly justified in comments.
- Color set size is derived from `init` and `end`; this assumes those arrays reflect all colors intended to be usable.
- The model includes an explicit search strategy in `solve :: seq_search(...)`, but this README intentionally focuses on model semantics rather than search behavior.
- No external citation is embedded in the model; the problem name in comments is **“Time-changing Graph Coloring Problem”**.

---

## Reference(s)
- Primary source in this folder: `tcgc2.mzn` (header comments and model content).
