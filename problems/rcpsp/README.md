# RCPSP (Resource-Constrained Project Scheduling Problem)

## What this model is about

This MiniZinc model encodes a **Resource-Constrained Project Scheduling Problem (RCPSP)**.

In plain terms:

- You have a set of tasks.
- Each task has a fixed duration.
- Some tasks must happen before others (precedence rules).
- Tasks consume limited shared resources (like workers or machines) while they run.

The goal is to build a valid schedule that finishes as early as possible.

## Inputs (data you provide)

The model expects:

- `n_res`: number of resources.
- `rc[r]`: capacity of each resource `r`.
- `n_tasks`: number of tasks.
- `d[i]`: duration of task `i`.
- `rr[r,i]`: amount of resource `r` required by task `i` while it runs.
- `suc[i]`: set of successor tasks that must start after task `i` finishes.

It also defines `sum_d = sum(d)`, used as a safe upper bound for time variables.

## Decision variables

- `s[i]` (start time of task `i`): integer variable in `0..sum_d`.
- `objective` (makespan): integer variable in `0..sum_d`, representing the project end time.

## Core constraints

1. **Precedence constraints**  
   For each precedence edge `i -> j`:  
   `s[i] + d[i] <= s[j]`  
   (task `j` cannot start before `i` ends).

2. **Pairwise non-overlap (redundant strengthening)**  
   If two tasks together would exceed capacity on at least one resource, they are forced not to overlap in time (one must be before the other).

3. **Resource capacity over time**  
   For each resource, a `cumulative(...)` constraint ensures that at every time point, total usage by running tasks does not exceed that resource’s capacity.

4. **Makespan definition**  
   Every task must finish by `objective`:  
   `s[i] + d[i] <= objective`.

## Objective

The model **minimizes** `objective`, i.e., minimizes the total project completion time (makespan).

## Output

The solver prints:

- `s = [...]` task start times
- `objective = ...` final makespan

## Notes for beginners

- This is a classic RCPSP formulation with time-index-free start-time variables and global cumulative resource constraints.
- The model includes additional (redundant) ordering constraints to strengthen propagation; they do not change the set of feasible schedules.
- This README intentionally does **not** explain solver search strategy details.

## Uncertainty and assumptions

- The model does not explicitly document whether task indices include dummy start/end activities; that depends on the input data files.
- The exact benchmark source is not explicitly cited in this folder, so the original instance provenance cannot be confirmed from this model alone.

## Possible references

If you want background reading, commonly cited RCPSP references include:

- Błażewicz, Lenstra, and Rinnooy Kan (1983), scheduling subject to resource constraints.
- Kolisch and Sprecher (1997), PSPLIB benchmark set for project scheduling.
- MiniZinc Handbook documentation for `cumulative` global constraint.
