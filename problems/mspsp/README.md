# Multi-Skilled Project Scheduling Problem (MSPSP)

## Problem Description

The **Multi-Skilled Project Scheduling Problem (MSPSP)** is a variant of the classic
Resource-Constrained Project Scheduling Problem (RCPSP). The goal is to schedule a
set of activities (tasks) so that the total project duration — called the **makespan**
— is minimised.

In the standard RCPSP, resources are interchangeable units (e.g., machines or
generic workers). MSPSP adds a richer, more realistic structure: each worker has a
specific set of skills, each task requires a certain number of workers possessing
each relevant skill, and every worker can only work on one task at a time. The
challenge is therefore not just _when_ to run each task, but also _who_ to assign to it.

This problem arises naturally in project management, construction planning, software
development scheduling, and any setting where human resources have heterogeneous
capabilities.

## Parameters

| Parameter       | Description                                                            |
| --------------- | ---------------------------------------------------------------------- |
| `n_skills`      | Total number of distinct skills                                        |
| `n_workers`     | Total number of available workers                                      |
| `n_tasks`       | Total number of tasks to be scheduled                                  |
| `has_skills[j]` | The set of skills possessed by worker `j`                              |
| `d[i]`          | Duration (number of time periods) of task `i`                          |
| `rr[k, i]`      | Number of workers with skill `k` required by task `i`                  |
| `suc[i]`        | Set of tasks that must start only after task `i` finishes (successors) |

A derived parameter `rc[k]` is also computed internally: the total number of workers
who possess skill `k`, providing the global capacity for each skill.

## Decision Variables

| Variable    | Description                                                        |
| ----------- | ------------------------------------------------------------------ |
| `s[i]`      | The start time of task `i` (an integer in `0..tmax`)               |
| `w[j, i]`   | A boolean indicating whether worker `j` is assigned to task `i`    |
| `objective` | The project makespan — the earliest time by which all tasks finish |

The planning horizon `tmax` is set to the sum of all task durations, which is a
trivial (worst-case) upper bound on when the project can finish.

## Constraints

1. **Precedence constraints** — If task `j` is a successor of task `i`, then task `j`
   cannot start until task `i` has finished: `s[i] + d[i] <= s[j]`.

2. **Skills requirements** — For every task `i` and every skill `k` needed by that
   task, enough workers who have skill `k` must be assigned to the task to satisfy
   the requirement `rr[k, i]`. Workers who have no relevant skill for a task cannot
   be assigned to it.

3. **Worker non-overlap** — Each worker can only work on one task at any given time.
   This is enforced via a `cumulative` constraint per worker over all tasks that
   worker is eligible to perform.

4. **Redundant ordering constraints** — For pairs of tasks that have no precedence
   relationship but collectively require more workers with some skill than are
   available globally, the model adds an implicit ordering: one must finish before
   the other starts. This tightens the problem without changing its solutions.

5. **Redundant skill-level cumulative constraints** — A `cumulative` constraint is
   also added for each skill, treating the total workers needed with that skill as a
   resource with capacity `rc[k]`. This further tightens the model.

6. **Makespan definition** — The objective variable is at least as large as the
   completion time of every task with no successors (i.e., every "final" task in the
   project).

## Objective

The model **minimises `objective`**, the project makespan — the point in time when
the last task completes.

## References

The MSPSP has been studied extensively in the scheduling literature. Relevant works
include:

- Bellenguez, O., & Néron, E. (2007). _Lower bounds for the multi-skill project
  scheduling problem_. In E. Burke & H. Rudová (Eds.), _Practice and Theory of
  Automated Timetabling VI_, Lecture Notes in Computer Science, vol. 3867, pp. 14–28.
  Springer. https://doi.org/10.1007/11593577_2

- Montoya, C., Bellenguez-Morineau, O., Pinson, É., & Rivreau, D. (2014).
  _Branch-and-price approach for the multi-skill project scheduling problem_.
  _Optimization Letters_, 8(5), 1721–1734. https://doi.org/10.1007/s11590-013-0692-2

- Correia, I., Lourenço, L. L., & Saldanha-da-Gama, F. (2012).
  _Project scheduling with flexible resources: Formulation and inequalities._
  _OR Spectrum_, 34(3), 635–663. https://doi.org/10.1007/s00291-010-0233-0

> **Note:** The exact data instances used with this model and the original source of
> this MiniZinc encoding are not fully documented here. If you know the specific
> benchmark library or paper from which the instances derive, please update this
> README accordingly.

## Model update summary

Added concise inline comments in mspsp.mzn to clarify:

- task start and worker assignment variable semantics,
- objective interpretation as minimized makespan,
- scheduling intent under skill and precedence constraints.
