# RCPSP/WET (Resource-Constrained Project Scheduling with Weighted Earliness/Tardiness)

## What problem is this model solving?

This MiniZinc model solves a **project scheduling** problem where:

- There are multiple tasks, each with a fixed duration.
- Some tasks must happen before others (precedence constraints).
- Tasks consume limited shared resources (like workers or machines).
- Each task has a **desired start time**.

The goal is to build a feasible schedule that respects precedence and resource limits, while starting tasks as close as possible to their desired times.

---

## Inputs (data)

The model expects:

- `n_res`, `rc[r]`: number of resources and each resource capacity.
- `n_tasks`, `d[i]`: number of tasks and duration of each task.
- `rr[r,i]`: amount of resource `r` required by task `i` while it runs.
- `suc[i]`: successor tasks of task `i` (defines precedence arcs).
- `deadline[i,1..3]`:
  - `deadline[i,1]`: desired start time of task `i`
  - `deadline[i,2]`: cost per unit time if task starts early
  - `deadline[i,3]`: cost per unit time if task starts late
- `t_max`: planning horizon upper bound.

---

## Decision variables

- `s[i]` (for each task `i`): start time of task `i`, with domain `0..t_max-1`.
- `objective`: total weighted earliness/tardiness cost.

---

## Core constraints

1. **Precedence**  
   For every precedence arc `i -> j`:  
   `s[i] + d[i] <= s[j]`

2. **Resource capacities (cumulative constraints)**  
   For each resource, overlapping running tasks cannot exceed capacity `rc[r]`.

3. **Redundant pairwise non-overlap (strengthening)**  
   If two tasks together would exceed some resource capacity, they are forced not to overlap.

4. **Objective definition constraint**  
   The model defines total penalty as:
   - earliness part: `deadline[i,2] * max(0, deadline[i,1] - s[i])`
   - tardiness part: `deadline[i,3] * max(0, s[i] - deadline[i,1])`

---

## Objective

Minimize:

- Sum of weighted earliness and tardiness penalties over all tasks.

Intuition:

- Starting too early can be bad (earliness cost).
- Starting too late can be bad (tardiness cost).
- Different tasks can have different early/late penalty weights.

---

## Notes and uncertainty

- The model uses desired **start** times (not due dates on completion), which is a specific WET variant.
- `t_max` is provided as input; quality/performance can depend on how tight this bound is.
- The comments mention an instance generator that sets horizon using an RCPSP makespan plus slack; this README assumes that convention but cannot verify generator details from this file alone.
- Semantics of `cumulative.mzn` follow standard MiniZinc global-constraint behavior.

---

## References (identifiable from model/comments)

- MiniZinc global constraint library: `cumulative.mzn`.
- Problem family: Resource-Constrained Project Scheduling Problem (RCPSP), extended with weighted earliness/tardiness (WET).
- Header attribution in the model: The University of Melbourne and NICTA (2009–2016).
