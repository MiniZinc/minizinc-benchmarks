# Multi-mode Resource-Constrained Project Scheduling (MRCPSP)

## Problem Description

The **Multi-mode Resource-Constrained Project Scheduling Problem (MRCPSP)** is a classic
optimisation problem in project management. You have a project made up of a set of
**activities** (tasks) that must be scheduled over time. The goal is to complete the entire
project as quickly as possible.

What makes this problem interesting — and difficult — are two key complications:

1. **Multiple modes**: Each activity can be carried out in one of several _modes_ (different
   ways of doing the job). For example, a task might be done quickly using many workers, or
   slowly using fewer workers. Each mode has its own duration and its own demand for resources.
   Exactly one mode must be chosen for each activity.

2. **Resource constraints**: Activities consume resources. Resources come in two kinds:
   - **Renewable resources** (e.g. workers, machines): their capacity resets each time period,
     but at no point in time can the total demand across all simultaneously active activities
     exceed the available capacity.
   - **Non-renewable resources** (e.g. raw materials, budget): they are consumed permanently,
     so the total consumption across all activities throughout the project must not exceed the
     total available supply.

Additionally, activities have **precedence constraints**: some activities must finish before
certain others can begin (e.g. you must lay foundations before building walls).

## Parameters

| Parameter | Description                                                       |
| --------- | ----------------------------------------------------------------- |
| `n_res`   | Number of resources                                               |
| `n_tasks` | Number of activities (tasks)                                      |
| `n_opt`   | Total number of modes across all activities                       |
| `rcap`    | Capacity of each resource                                         |
| `rtype`   | Resource type: `1` = renewable, `2` = non-renewable               |
| `modes`   | The set of available modes for each activity                      |
| `dur`     | Duration of each mode                                             |
| `rreq`    | Resource requirement for each (resource, mode) pair               |
| `succ`    | Successor activities for each activity (precedence relationships) |

## Decision Variables

| Variable     | Description                                                                                        |
| ------------ | -------------------------------------------------------------------------------------------------- |
| `start[i]`   | The time at which activity `i` begins                                                              |
| `mrun[m]`    | Whether mode `m` is the chosen mode for its activity (`true`/`false`)                              |
| `adur[i]`    | The actual duration of activity `i` (determined by the selected mode)                              |
| `arreq[k,i]` | The actual resource requirement of activity `i` for resource `k` (determined by the selected mode) |
| `objective`  | The project makespan — the time at which all activities have finished                              |

## Constraints

- **Mode selection**: Exactly one mode is selected per activity. The duration and resource
  requirements of an activity take the values corresponding to the chosen mode.
- **Precedence**: For every pair of activities where one must follow the other, the predecessor
  must finish before the successor can start.
- **Renewable resource capacity**: At every point in time, the total demand on each renewable
  resource from all concurrently running activities must not exceed that resource's capacity.
  This is enforced using the `cumulative` global constraint.
- **Non-renewable resource capacity**: The total consumption of each non-renewable resource
  across all activities must not exceed its total supply.
- **Non-overlapping constraints** (redundant): Additional constraints are posted between pairs
  of activities that cannot run simultaneously (due to resource conflicts), to help the solver
  find solutions faster. These are logically implied by the resource constraints but make
  solving more efficient.

## Objective

**Minimise the makespan**: the time at which the last activity finishes, i.e.

$$\text{objective} = \max_{i \in \text{Act},\; \text{succ}[i] = \emptyset} (\text{start}[i] + \text{adur}[i])$$

The makespan is computed over all activities with no successors (i.e. the activities that
complete last in any ordering consistent with the precedence constraints).

## Benchmark Instances

The data instances use the `j30` naming convention, referring to the well-known **PSPLIB**
benchmark set for MRCPSP with 30 activities. Each instance has 4 resources and up to 3 modes
per activity.

## References

- Szeredi, R., & Schutt, A. (2016). _Improving and Extending the MRCPSP_. In Proceedings of
  the 22nd International Conference on Principles and Practice of Constraint Programming
  (CP 2016), Lecture Notes in Computer Science, vol. 9892, pp. 577–594. Springer, Cham.
  _(This MiniZinc model was developed by the authors of this paper.)_

- Kolisch, R., & Sprecher, A. (1997). _PSPLIB — A project scheduling problem library_.
  European Journal of Operational Research, 96(1), 205–216.
  _(Source of the `j30` benchmark instances.)_

- Sprecher, A., & Drexl, A. (1998). _Multi-mode resource-constrained project scheduling by a
  simple, general and powerful sequencing algorithm_. European Journal of Operational Research,
  107(2), 431–450.
