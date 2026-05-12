# EchoSched: Energy-Aware Job Shop Scheduling with Speed Scaling

## Problem Description

This model addresses an **energy-aware job shop scheduling problem (JSP) with speed scaling**. It extends the classical job shop scheduling problem by allowing each operation to be executed at different speed levels, creating a trade-off between time and energy consumption.

In a standard job shop scheduling problem, a set of jobs must each be processed through a sequence of machines in a prescribed order. Each job visits every machine exactly once, and no two jobs can use the same machine at the same time. The goal is typically to minimise the total time needed to complete all jobs (the _makespan_).

This model adds an energy dimension: each operation can be run faster or slower. Running an operation faster takes less time but consumes more energy; running it slower saves energy but takes longer. The solver must decide both _when_ to schedule each operation and _at what speed_ to run it, balancing total completion time against total energy usage.

## Model Parameters

| Parameter          | Description                                                                                                              |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------ |
| `JOBS`             | The set of jobs to be scheduled                                                                                          |
| `MACHINES`         | The set of machines available for processing                                                                             |
| `SPEED`            | The number of available speed levels (speeds are indexed from 1 to `SPEED`)                                              |
| `time[j, m, s]`    | The processing time of job `j` on machine `m` when run at speed level `s`                                                |
| `energy[j, m, s]`  | The energy consumed by job `j` on machine `m` when run at speed level `s`                                                |
| `precedence[j, m]` | The position of machine `m` in the processing sequence for job `j` (a lower number means the machine is visited earlier) |

## Decision Variables

| Variable             | Description                                                                      |
| -------------------- | -------------------------------------------------------------------------------- |
| `start_time[j, m]`   | The time at which job `j` begins processing on machine `m`                       |
| `SpeedScaling[j, m]` | The speed level chosen for job `j` on machine `m` (an integer from 1 to `SPEED`) |

## Constraints

1. **Precedence (operation ordering):** For each job, its operations must be performed in the order specified by the `precedence` array. An operation cannot begin until the previous operation in the job's sequence has finished.

2. **Machine capacity (no overlap):** At most one job can use a given machine at any point in time. If two jobs both require the same machine, one must finish before the other begins.

## Objective

The model minimises the combined sum of two quantities:

- **Makespan (`makespan`):** The time at which the last operation across all jobs and machines finishes, i.e., `max(start_time[j,m] + time[j,m,SpeedScaling[j,m]])` over all jobs and machines.
- **Total energy (`consumedEnergy`):** The sum of energy consumed by every operation across all jobs and machines.

$$\text{minimise} \quad \text{makespan} + \text{consumedEnergy}$$

This combined objective means the solver must find a balance: speeding up operations reduces the makespan but increases energy consumption, while slowing them down saves energy but may push the makespan higher.

> **Note:** The weighting of makespan versus energy is equal (both are summed directly). Depending on the units used in the data, the relative importance of each term may vary across instances. An expert familiar with the original problem source may be able to clarify the intended units and scaling.

## Problem Origin

This problem was used in the **MiniZinc Challenge 2025**. The "EchoSched" name suggests it may originate from research into energy-aware scheduling. Speed scaling as a technique for energy-efficient scheduling has been widely studied in the combinatorial optimisation literature (e.g., in the context of processors that can operate at variable frequencies). The specific source paper for this benchmark instance set is not confirmed; if you are aware of the original reference, please update this README.

## Instance Format

The data instances are named using the pattern `{jobs}-{machines}-?-{speeds}_{id}.json`. For example:

- `12-12-0-1_7.json` — 12 jobs, 12 machines, 1 speed level, instance 7
- `13-14-0-2_6.json` — 13 jobs, 14 machines, 2 speed levels, instance 6

The meaning of the third numeric field (shown as `0` in the examples above) is not confirmed. It may represent a problem variant or generation parameter.

## Model update summary

Added concise inline comments in JSP0.mzn to clarify:

- operation-level start-time and speed-scaling decision variables,
- derived makespan and energy expressions,
- combined objective interpretation (time + energy).
