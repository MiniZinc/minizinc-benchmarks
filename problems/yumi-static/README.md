# YuMi Static Dual-Arm Robot Scheduling

## Problem Description

This model schedules assembly tasks for the **ABB YuMi**, a collaborative dual-arm robot
commonly used in industrial automation. The robot has two arms — a left arm and a right arm —
each of which must visit a set of *locations* (trays, fixtures, cameras, output stations) to
perform assembly sub-tasks. The goal is to minimise the **cycle time**: the time it takes for
both arms together to complete one full repetition of the assembly.

The schedule is *static* in the sense that a single fixed ordering (a cyclic schedule) is
computed offline and then repeated indefinitely on the real robot. "Static" distinguishes this
from a reactive or online scheduling setting.

## Key Concepts

| Concept | Meaning |
|---------|---------|
| **Agent** | One of the two robot arms (left = 1, right = 2) |
| **Task** | An atomic assembly operation (pick, place, inspect, …) |
| **Location** | A physical station on the work-table |
| **Hamiltonian circuit** | The task sequence is modelled as a single circuit over all tasks for both arms, split by dummy start/end nodes |
| **Period** | The time from when an arm starts until it has completed all its tasks (the repeating cycle length) |
| **Makespan** | `period + cycle_overlap`, where `cycle_overlap` is the offset between the two arms' start times |

## Decision Variables

- `agent[t]` — which arm (1 or 2) performs task *t*
- `location[t]` — where task *t* is carried out (some tasks have a fixed location type; the exact station may still be chosen)
- `successor[t]` / `task[i]` — two equivalent encodings of the task ordering: `successor[t]` gives the next task after *t*; `task[i]` gives the *i*-th task in the global sequence
- `arrival_time[t]` — when the assigned arm arrives at the location for task *t*
- `start_time[t]`, `end_time[t]` — when processing of task *t* begins and ends
- `duration[t]` — processing time of task *t* (depends on which arm is assigned)
- `travel_time[t]` — time for the arm to travel from task *t* to its successor
- `waiting_time[t]` — idle time between arrival and start (needed for collision safety)
- `period`, `makespan`, `cycle_overlap` — aggregate timing variables used in the objective

## Constraints

1. **Hamiltonian circuit** — the successor array forms a single circuit visiting every task exactly once, split into two arm sub-sequences via dummy start/end depot tasks.
2. **Agent assignment** — tasks within the same pick-and-place sequence (gripper or suction) must be assigned to the same arm; depot tasks are fixed to their respective arm.
3. **Location types** — tray tasks go to tray locations, camera tasks to camera locations, fixture tasks to fixture locations, output tasks to output locations.
4. **Fixture co-location** — all sub-tasks belonging to the same fixture must happen at the *same* fixture station; different fixtures must occupy *different* stations.
5. **Task duration depends on arm** — each arm has its own timing table; duration is determined by the `(arm, task)` pair.
6. **Travel time depends on arm and locations** — separate travel-time matrices are provided for left and right arms.
7. **Ordering within sequences** — fixture sub-tasks, suction pick-and-place, and gripper pick-and-place must follow a prescribed ordering.
8. **Tool capacity** — gripper load is tracked (≤ 1 object held) and suction cups are counted (≤ `no_suction_cups`); some tasks require an empty gripper on arrival.
9. **Collision avoidance** — the workspace is linearly ordered; the left arm only accesses locations to its side and the right arm to its side, preventing the two arms from physically colliding.
10. **Cyclic feasibility** — each fixture assembly must be finished before the next cycle begins; both arms' cycle lengths equal `period`.

## Objective

**Minimise `period`** — the repeating cycle time of the assembly, which directly determines
the robot's throughput.

## Uncertainty / Notes

- The model references a "CPAIOR-paper" (in code comments) but does not name it explicitly.
  The author is **Johan Ludde Wessén** (2021). The paper is likely associated with CPAIOR 2021
  or a related venue; the exact citation is not embedded in the model file.
- Several implied constraints (`implied_cumulative`, `implied_diffn`, `implied_value_precede`)
  are optional flags that can be toggled via Boolean parameters in the data file. Their effect
  on solver performance may vary by instance.
- Travel times use the value `-1` to indicate that a location is *unreachable* by a given arm,
  encoding the physical workspace limits of each arm.

## Model update summary

Added concise inline comments in yumi-static.mzn to clarify:

- task assignment, sequence, and timing decision variable semantics,
- precedence and workspace-feasibility constraints,
- objective intent as minimizing cycle period.

## References

- Johan Ludde Wessén, *YuMiScheduler* model, 2021.
  MIT License. See [LICENSE](LICENSE).
- ABB YuMi dual-arm collaborative robot: <https://new.abb.com/products/robotics/collaborative-robots/irb-14000-yumi>
