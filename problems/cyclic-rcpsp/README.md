# Cyclic Resource-Constrained Scheduling (RCMSP)

## Problem Description

The **Resource-Constrained Modulo Scheduling Problem (RCMSP)** is a cyclic scheduling problem. Instead of scheduling a set of tasks just once, the same set of tasks is assumed to repeat indefinitely — each repetition is called an _iteration_. The goal is to find a _periodic_ schedule: a fixed pattern that can be tiled indefinitely, such that no resource is ever overloaded and all ordering constraints between tasks are satisfied.

This kind of problem arises in contexts such as compiler optimisation for pipelined processors, where a loop body (the repeating set of tasks) must be scheduled to run as fast as possible while respecting data dependencies and hardware resource limits.

### Key Concepts

- **Period**: The time interval after which the entire schedule repeats. A shorter period means more throughput — tasks are completed more frequently. This is the primary thing being minimised.
- **Makespan**: The span of time from the first task to the last task within a single iteration. This is the secondary objective (minimised after the period).
- **Tasks**: Each task has a duration of 1 time unit, except for two artificial bookkeeping tasks — a _source_ (task 1) and a _sink_ (task `n_tasks`) — which have zero duration. The source and sink represent the notional start and end of each iteration.
- **Resources**: Shared resources (e.g., functional units, memory bandwidth) each have a fixed capacity. Tasks consume some amount of each resource while running, and the total consumption at any point in time must not exceed the capacity.
- **Generalised Precedence Relations**: These are ordering constraints between tasks. Unlike simple "task A must finish before task B starts" constraints, these express _minimum time lags_ between tasks across potentially different iterations. Specifically, a constraint of the form `s[i, k] + latency ≤ s[j, k + distance]` says: the start of task `j` in iteration `k + distance` must be at least `latency` time units after the start of task `i` in iteration `k`.

---

## Model Parameters

| Parameter       | Description                                                                      |
| --------------- | -------------------------------------------------------------------------------- |
| `n_res`         | Number of resources                                                              |
| `rcap[r]`       | Capacity of resource `r`                                                         |
| `n_tasks`       | Number of tasks (including source task 1 and sink task `n_tasks`)                |
| `rreq[i, r]`    | Amount of resource `r` required by task `i`                                      |
| `n_prec`        | Number of precedence relations                                                   |
| `prec[p, 1..4]` | Precedence relation `p`: task index `t1`, task index `t2`, latency, and distance |

---

## Decision Variables

| Variable | Description                                                         |
| -------- | ------------------------------------------------------------------- |
| `s[i]`   | Start time of task `i` within the schedule (an integer time slot)   |
| `k[i]`   | Iteration number to which task `i` belongs in the unrolled schedule |

From these, two derived quantities are computed:

- **`makespan`**: The time span covered by all real tasks within one iteration, computed as the difference between the latest and earliest adjusted start times.
- **`objective`**: A combined value encoding both goals — `s[n_tasks] * t_max + makespan` — so that minimising it first minimises the period and then (as a tiebreaker) the makespan.

---

## Constraints

1. **Generalised Precedence Constraints**: For each precedence relation, the start times and iteration assignments of the two tasks must satisfy the required time lag across the appropriate iterations.

2. **Non-overlapping (Redundant)**: If two tasks together require more of some resource than is available, they cannot run at the same time. This constraint is redundant (implied by the cumulative constraint) but is included to help the solver.

3. **Cumulative Resource Constraints**: For each resource, the total demand from all concurrently running tasks must never exceed the resource capacity. This uses the global `cumulative` constraint.

4. **Period Constraints**: All tasks must complete before the sink task's start time (which defines the period). The sink task's iteration is set to the maximum iteration number across all tasks.

5. **Symmetry Breaking**: The source task is fixed to start at time 0 in iteration 0, removing equivalent shifted solutions.

---

## Objective

The model uses a **lexicographic minimisation** of two objectives, encoded as a single integer:

$$\text{objective} = \text{period} \times t\_\text{max} + \text{makespan}$$

This ensures the solver first minimises the _period_ (how often the task set repeats) and then, among schedules with the same period, minimises the _makespan_ (the time span within one iteration).

---

## References

This model was developed at the **University of Melbourne and NICTA** (2011) and appeared in the MiniZinc Challenges of 2011 and 2014.

The RCMSP is closely related to classical cyclic scheduling theory. Relevant background can be found in:

- Hanen, C., & Munier, A. (1995). _A study of the cyclic scheduling problem on parallel processors_. Discrete Applied Mathematics, 57(2–3), 167–192.
- Rau, B. R. (1994). _Iterative modulo scheduling: An algorithm for software pipelining loops_. Proceedings of the 27th Annual International Symposium on Microarchitecture (MICRO-27).
- Dinechin, B. D. (1996). _Parametric computation of margins and of minimum cumulative register lifetime dates_. ACM SIGPLAN Notices, 31(7), 141–151.

> **Note**: The exact origin of this specific benchmark instance set is uncertain. If you are familiar with the data source, please update this section.

## Model update summary

Added concise inline comments in rcmsp.mzn to clarify:

- start-time and iteration variable semantics,
- encoded lexicographic objective structure,
- optimization intent (period first, makespan second).
