# Aircraft Disassembly Scheduling

## Problem Description

When an aircraft reaches the end of its service life, it must be carefully dismantled so that parts can be recycled, reused, or safely disposed of. This process — called **aircraft disassembly** — involves many individual tasks, each requiring specialist workers with the right skills, performed in the right order, and completed as quickly and cheaply as possible.

This model schedules the disassembly of an aircraft by deciding:

- **When** each task should start, and
- **Which workers** should be assigned to each task.

The goal is to minimise a combined cost that strongly prioritises finishing all tasks as quickly as possible (minimising _makespan_), while also keeping the total labour cost low.

This model is inspired by a CP Optimizer model for Aircraft Disassembly Scheduling and the Multi-Skill Project Scheduling Problem (MSPSP) literature. See the references section below.

---

## Parameters (Input Data)

| Parameter                                                               | Description                                                      |
| ----------------------------------------------------------------------- | ---------------------------------------------------------------- |
| `nActs`                                                                 | Number of disassembly tasks/activities                           |
| `nResources`                                                            | Number of available workers                                      |
| `nSkills`                                                               | Number of distinct skill types                                   |
| `nPrecs`                                                                | Number of precedence relationships between tasks                 |
| `maxt`                                                                  | Maximum allowed time horizon (latest possible finish time)       |
| `dur[a]`                                                                | Duration of task `a`                                             |
| `sreq[a,s]`                                                             | How many workers with skill `s` are needed for task `a`          |
| `mastery[r,s]`                                                          | Whether worker `r` has mastered skill `s`                        |
| `resource_cost[r]`                                                      | Cost per time unit of employing worker `r`                       |
| `pred[p]`, `succ[p]`                                                    | Predecessor and successor tasks for precedence `p`               |
| `loc[a]`                                                                | The physical location on the aircraft where task `a` takes place |
| `loc_cap[l]`                                                            | Maximum number of workers allowed at location `l` simultaneously |
| `occupancy[a]`                                                          | Number of worker-slots task `a` occupies at its location         |
| `mass[a]`                                                               | The mass removed from the aircraft by task `a`                   |
| `maxDiff[m]`                                                            | Maximum allowed imbalance for mass balance constraint `m`        |
| `unavailable_resource[i]`, `unavailable_start[i]`, `unavailable_end[i]` | A worker who is unavailable during a given time window           |

---

## Decision Variables

| Variable         | Description                                                                                  |
| ---------------- | -------------------------------------------------------------------------------------------- |
| `start[a]`       | The start time of task `a`                                                                   |
| `assign[a,r]`    | `true` if worker `r` is assigned to task `a`                                                 |
| `contrib[a,r,s]` | `true` if worker `r` contributes skill `s` to task `a`                                       |
| `overlap[u]`     | `true` if a pair of unrelated tasks (with no direct precedence between them) overlap in time |

---

## Constraints

1. **Precedence**: Certain tasks must be fully completed before dependent tasks can begin (e.g., you must remove a panel before accessing the components beneath it).

2. **Skill requirements**: Each task needs a specific number of workers with each required skill type. Workers can only contribute skills they have mastered, and each worker contributes at most one skill per task.

3. **Worker availability**: Some workers may be unavailable during certain time windows (e.g., due to shift patterns or other commitments). Tasks assigned to such workers must be scheduled outside those windows.

4. **Location capacity**: Each physical location on the aircraft has a maximum number of workers that can work there at the same time. Tasks at the same location must not collectively exceed this limit.

5. **Mass balance**: As parts are removed from the aircraft, the left-right (or other axis) weight balance must remain within a safe range at all times. This ensures structural and safety requirements are met throughout the disassembly process. Tasks are ordered implicitly through a constraint on cumulative mass removal.

6. **Non-overlap for resource-conflicting tasks**: Two tasks that are unrelated by precedence but compete for the same scarce skill are forced to be sequenced rather than overlapping.

---

## Objective

The model minimises a **weighted combination**:

$$\text{objective} = 100000 \times \text{makespan} + \sum_{a, r} \text{resource\_cost}[r] \times \text{dur}[a] \times \text{assign}[a, r]$$

The large weight on makespan (100,000) means the primary goal is to **finish as early as possible**, while the labour cost term acts as a secondary tie-breaker to prefer cheaper worker assignments among equally fast schedules.

---

## References

- Thomas, C. F., & others. _Aircraft Disassembly Scheduling (CP Optimizer model)_. GitHub repository: [cftmthomas/AircraftDisassemblyScheduling](https://github.com/cftmthomas/AircraftDisassemblyScheduling)

- Young, K. D., & others. _Multi-Skill Project Scheduling Problem instance library (MiniZinc model)_. GitHub repository: [youngkd/MSPSP-InstLib](https://github.com/youngkd/MSPSP-InstLib)

- Zhong, A. (2022). _Aircraft Disassembly Scheduling — Constraint Programming model_ (this model's author attribution).

> **Note for reviewers**: The exact academic paper(s) that introduced this specific aircraft disassembly formulation were not conclusively identified. If you are aware of a direct publication, please add the full citation here.
