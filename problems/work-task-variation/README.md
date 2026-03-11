# Work Task Variation

## Problem Description

The Work Task Variation problem is a workforce scheduling problem. A set of **workers** (called *Resources*) must each be assigned a sequence of **activities** (tasks) across a fixed number of **time slots**. Each worker's schedule must form a single contiguous block of work — they may be idle (represented as `None`) before and after their shift, but cannot have gaps in the middle.

Within their shift, a worker's activity may change from slot to slot. A **run** is a maximal sequence of consecutive slots where a worker performs the same activity. The goal is to minimise a cost that penalises both how long individual runs are and how frequently each activity occurs per worker.

## Input Data

| Parameter | Description |
|---|---|
| `Resources` | Enumeration of workers |
| `Activities` | Enumeration of task types |
| `slots` | Number of time slots in the schedule |
| `requirements[a, s]` | How many workers must perform activity `a` at slot `s` |
| `fixed[r, s]` | Pre-assigned activity for worker `r` at slot `s` (if any) |
| `activity_run_cost[a, len]` | Cost of a run of activity `a` with length `len` |
| `activity_frequency_cost[a, k]` | Cost when a worker performs activity `a` exactly `k` times (i.e. `k` runs) |

## Decision Variables

| Variable | Description |
|---|---|
| `schedule[r, s]` | The activity (or `None`) assigned to worker `r` at slot `s` |
| `run_end[r, s]` | `true` when slot `s` is the last slot of a run for worker `r` |
| `run_length[r, s]` | The length of the current run at slot `s` for worker `r` |
| `run_cost[r, s]` | Cost charged at the end of each run; zero mid-run |
| `frequency_cost[r, a]` | Cost for how many times worker `r` performs activity `a` |

## Constraints

- **Structural:** Each worker's schedule matches the regular pattern `None* [^None]* None*` — a single contiguous block of non-idle work.
- **Coverage:** At every slot, the number of workers assigned to each activity (or idle) must exactly match the given `requirements` (enforced via `global_cardinality`).
- **Fixed assignments:** Some worker–slot pairs have a pre-determined activity that must be respected.
- **Run tracking:** Run lengths are computed incrementally; a run cost is incurred at the end of each run based on its length and activity type.
- **Frequency costs:** Each worker incurs an additional cost based on how many distinct runs of each activity they perform across their shift.

## Objective

**Minimise** the total cost:

$$\text{objective} = \sum_{r,s} \text{run\_cost}[r, s] + \sum_{r,a} \text{frequency\_cost}[r, a]$$

This encourages schedules where workers perform longer, less-interrupted runs of activities and do not switch tasks too frequently, while simultaneously discouraging overly long runs if the cost tables are shaped that way — the exact trade-off is instance-dependent.

## Notes and Uncertainty

- The specific cost values in `activity_run_cost` and `activity_frequency_cost` vary per instance, so the balance between preferring long runs vs. many short runs depends entirely on the data.
- Instance filenames encode parameters such as schedule length, number of open (non-fixed) slots, number of workers, and a block-size parameter used during generation.
- The problem appeared in the **MiniZinc Challenge 2025**.

## References

- MiniZinc Challenge 2025: [https://www.minizinc.org/challenge/](https://www.minizinc.org/challenge/)
- Original model authors: Mikael Zayenz Lagerkvist and Magnus Rattfeldt (2025)
