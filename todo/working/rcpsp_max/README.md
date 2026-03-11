# rcpsp_max

## What problem does this model solve?

This model encodes the **Resource-Constrained Project Scheduling Problem with minimal and maximal time lags (RCPSP/max)**.

In plain terms:

- You have a set of activities (tasks), each with a fixed duration.
- Tasks consume limited renewable resources (like workers or machines) while they run.
- Some pairs of tasks must satisfy timing relations of the form:
  - task `j` must start at least/at most some offset from task `i`.
- The goal is to build a feasible schedule that finishes the project as early as possible.

The model uses discrete time and non-preemptive tasks (once a task starts, it runs to completion).

## Inputs (data)

Key input parameters are:

- `n_res`, `n_tasks`, `n_dc`: number of resources, tasks, and difference constraints.
- `rcap[res]`: capacity of each resource.
- `dur[i]`: duration of each task.
- `rr[res, i]`: amount of resource `res` required by task `i` while it executes.
- `dcons[idx, 1..3]`: precedence/difference constraints in the form:
  - `s[x] + c <= s[y]` where row = `(x, c, y)`.

A simple upper bound `t_max` is computed from durations and lag values, then start times are restricted to `0..t_max`.

## Decision variables

- `s[i]`: start time of task `i` (integer time point).
- `objective`: makespan (project completion time).

## Constraints (high-level)

1. **Difference constraints**  
   Every row in `dcons` enforces `s[x] + c <= s[y]`.

2. **Redundant pairwise non-overlap constraints**  
   For task pairs that cannot overlap due to resource limits, the model adds ordering logic (`i` before `j`, `j` before `i`, or a Boolean choice).  
   These are strengthening constraints to help propagation.

3. **Cumulative resource constraints**  
   For each resource, `cumulative(...)` ensures the total simultaneous demand never exceeds capacity.

4. **Makespan linking**  
   For each task, `s[i] + dur[i] <= objective`, so `objective` is at least every task’s finish time.

## Objective

The solve goal is:

- **Minimize** `objective` (the project makespan).

So the solver looks for the earliest possible completion time while respecting all timing and resource limits.

## Search strategy note

The MiniZinc model includes an explicit search annotation (`int_search` on start times, first-fail, min-value).  
This README intentionally does **not** explain or evaluate search strategy details, focusing instead on problem meaning and model structure.

## Uncertainty / interpretation notes

- The model clearly states difference constraints as `s[x] + c <= s[y]`; depending on the dataset encoding, this can represent either minimum or maximum lag effects (or both through transformed constraints).
- The computed `t_max` is described as a “trivial upper bound”; tightness can vary by instance.
- No separate benchmark paper citation is embedded in this folder, so provenance is inferred from in-file comments and metadata.

## Identifiable references

- Model header comment credits: **The University of Melbourne and NICTA (2010)**.
- Uses MiniZinc global constraint: `cumulative` (from `globals.mzn`).
- Folder metadata (`metadata.json`) marks this as a minimization benchmark challenge entry (2010 instances).
