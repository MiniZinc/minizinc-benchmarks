# RCPSP/WET (Diverse Pareto Set) — Beginner-Friendly Guide

## What problem is this model solving?

This model schedules project tasks under **limited shared resources** and **precedence rules**:

- Each task has a fixed duration.
- Some tasks must finish before others can start.
- Tasks consume resource capacity while running.

Unlike a single-objective schedule, this model uses two competing criteria:

1. **Earliness**: starting a task before its desired start time (penalized).
2. **Tardiness**: starting a task after its desired start time (penalized).

So this is a **bi-objective** variant of RCPSP called **RCPSP/WET** (Weighted Earliness/Tardiness).

---

## Key inputs (data)

- `n_res`, `rc[r]`: number of resources and each resource capacity.
- `n_tasks`, `d[i]`: number of tasks and durations.
- `rr[r,i]`: resource demand of task `i` on resource `r`.
- `suc[i]`: successor tasks that must start after task `i` completes.
- `deadline[i,1..3]`:
  - desired start time,
  - earliness cost per time unit,
  - tardiness cost per time unit.
- `t_max`: planning horizon.

Diversity-related inputs:

- `nsols`: number of schedules to generate.
- `emin`, `emax`, `tmin`, `tmax`: bounds for objective-space grid.

---

## Decision variables (what the solver chooses)

- `st[s,i]`: start time of task `i` in solution `s`.
- `objectives[1,s]`, `objectives[2,s]`: earliness and tardiness of solution `s`.
- `dominated[e,t]`: whether objective point `(e,t)` is dominated by at least one produced solution.
- `objective`: total number of dominated points (hypervolume on a grid).

---

## Constraints in plain language

For each generated solution:

- **Precedence**: if `j` is a successor of `i`, then `start(i)+duration(i) <= start(j)`.
- **Resource feasibility**:
  - Pairwise non-overlap is added as a redundant strengthening constraint when two tasks cannot overlap on any resource.
  - Global `cumulative(...)` constraints enforce resource capacities over time.
- **Objective computation**:
  - Earliness = weighted sum of how much tasks start before target times.
  - Tardiness = weighted sum of how much tasks start after target times.

Across multiple solutions:

- Two solutions are fixed as extreme points (`(emin,tmax)` and `(emax,tmin)`).
- No solution may be dominated by another generated solution.
- The model maximizes how much of the `(earliness, tardiness)` grid is dominated by the set, yielding a **diverse Pareto approximation**.

---

## Objective

The solver **maximizes** `objective = sum(dominated)`, i.e., an approximation of Pareto hypervolume on a discrete objective grid.

In beginner terms: it tries to produce a _set_ of schedules that covers trade-offs between earliness and tardiness as broadly as possible.

---

## About uncertainty

This specific model is **deterministic**: durations, capacities, and target times are fixed constants from input data.

Practical uncertainty (for example, unexpected delays or changing resource availability) is **not modeled directly** here. Instead, the model helps by providing multiple trade-off schedules; a planner can pick among them if reality changes.

---

## Notes

- The file contains a search annotation (`int_search(...)`), but this README intentionally focuses on model meaning rather than search strategy details.
- Output prints all task start times for each solution and the final hypervolume-like score.

---

## References / provenance

Identifiable from the model source:

- Header states: Copyright (C) 2009–2016 The University of Melbourne and NICTA.
- Uses MiniZinc global constraint library: `cumulative.mzn`.
- Problem class: RCPSP/WET (Resource-Constrained Project Scheduling with Weighted Earliness/Tardiness).

No explicit paper citation is embedded in this `.mzn` file.
