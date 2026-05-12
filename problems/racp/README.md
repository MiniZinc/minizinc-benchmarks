# Resource Availability Cost Problem (RACP)

This MiniZinc model solves the **Resource Availability Cost Problem** (also called the **Resource Investment Problem**).

In plain terms:

- You have a set of tasks.
- Some tasks must happen before others (precedence constraints).
- Tasks consume renewable resources while they run.
- Each resource has a per-unit availability cost.
- You must choose task start times and resource capacities so all tasks finish by the planning horizon, while total resource availability cost is as small as possible.

## What the model takes as input

Key input parameters in `racp.mzn`:

- `n_tasks`, `dur`: number of tasks and each task duration.
- `succ`: immediate successor tasks (precedence graph).
- `n_res`, `rr`: number of resources and per-task resource demand (`rr[r,i]`).
- `cost`: cost per unit of each resource.
- `t_max`: end of planning horizon.

The model also derives helpful bounds and graph relations, such as:

- lower/upper bounds on resource capacity (`lb_usage`, `ub_usage`),
- transitive predecessor/successor sets (`all_prec`, `all_succ`),
- heuristic upper bounds from earliest/latest schedules (`rusage_es`, `rusage_ls`).

## Decision variables

The solver chooses:

- `s[i]`: start time of task `i` (within `0..t_max`).
- `rcap[r]`: capacity (available units) of resource `r`.
- `objective`: total resource availability cost.

## Core constraints

1. **Time feasibility**
   - Every task must end by the horizon: `s[i] + dur[i] <= t_max`.

2. **Precedence**
   - If `j` is a successor of `i`, then `i` must finish before `j` starts.

3. **Resource feasibility (cumulative)**
   - For each resource, overlapping tasks cannot consume more than chosen capacity `rcap[r]`.
   - Implemented with MiniZinc’s `cumulative` global constraint.

4. **Objective definition**
   - `objective = sum_r cost[r] * rcap[r]`.

5. **Extra valid upper bounds on objective**
   - The model adds bounds computed from earliest-start and latest-completion schedules, helping prune search.

## Objective

The model minimizes:

\[
\text{objective} = \sum\_{r \in Res} cost[r] \cdot rcap[r]
\]

Important modeling detail: cost is charged for **available capacity**, not actual realized utilization over time.

## Output

The model prints:

- `s` (task start times),
- `rcap` (chosen resource capacities),
- `objective` (minimum total availability cost found).

## Notes and uncertainty

- This explanation is based on the model source only; no instance files were inspected here.
- The model contains recursive helper functions (`all_succs`, `est`, `lct`) and comments noting these are not the most efficient implementations for large task sets.
- One comment says a cumulative-related part “will not bind” resource capacity directly; interpretation of performance impact can depend on solver and data.
- Search annotations exist in the model but are intentionally not discussed here (per request).

## Reference

The model header states it is derived from:

- Stefan Kreter, Andreas Schutt, Peter J. Stuckey, Jürgen Zimmermann (2018). _Mixed-integer Linear Programming and Constraint Programming Formulations for Solving Resource Availability Cost Problems_. European Journal of Operational Research, 266(2), 472–486. https://doi.org/10.1016/j.ejor.2017.10.014

## Model update summary

Added concise inline comments in racp.mzn to clarify:

- task start and resource capacity decision variable semantics,
- cumulative/precedence modeling role for feasibility,
- minimization intent for resource availability cost.
