# Artificial Teeth Scheduling Problem (ATSP)

## Problem Description

This model addresses the **Artificial Teeth Scheduling Problem (ATSP)**, a real-world production scheduling problem from artificial teeth manufacturing. The goal is to plan a sequence of production jobs on injection-moulding machines so that customer orders are fulfilled on time, production waste is minimised, and the total time to complete all work is as short as possible.

In artificial teeth manufacturing, plastic teeth are produced by injecting coloured material into metal **moulds**. Each mould has a fixed shape (making it compatible with only one production **program**), and different colors can be run through the same mould. Jobs are run one after another in a single sequence, with a setup time required between consecutive jobs (longer if the programs differ).

This model was used in the **MiniZinc Challenge 2021** and is based on the following paper:

> Winter, S., Kl­etzander, L., Prandtstetter, M., & Musliu, N. (2021).
> **Automated Production Scheduling for Artificial Teeth Manufacturing.**
> _Proceedings of the International Conference on Automated Planning and Scheduling (ICAPS)_, 31, 405–413.
> https://ojs.aaai.org/index.php/ICAPS/article/view/15997

The instances are based on real-life data, slightly scaled down to be tractable for exact solvers.

---

## Inputs

| Parameter                                  | Description                                                     |
| ------------------------------------------ | --------------------------------------------------------------- |
| `num_programs`                             | Number of distinct production programs (machine configurations) |
| `num_moulds`                               | Number of mould types available                                 |
| `num_colors`                               | Number of colours that can be produced                          |
| `num_demands`                              | Number of customer orders to fulfil                             |
| `num_lines`                                | Number of production lines                                      |
| `max_jobs`                                 | Maximum number of jobs in the schedule                          |
| `slots_per_program`                        | How many mould slots each program uses per cycle                |
| `cycle_time_for_program`                   | Duration of one production cycle for each program               |
| `available_moulds`                         | How many moulds of each type are available                      |
| `program_for_mould`                        | Which program each mould is compatible with                     |
| `line_for_mould`                           | Which production line each mould belongs to                     |
| `color_compatibility`                      | Which pairs of colours can appear in the same job               |
| `demand_qty`                               | Quantity required for each customer order                       |
| `demand_duedate`                           | Due date (in time units) for each customer order                |
| `demand_color`                             | Colour required by each customer order                          |
| `demand_mould`                             | Mould type required by each customer order                      |
| `sequence_setup_time`                      | Setup time when the same program continues job-to-job           |
| `program_setup_time`                       | Setup time when switching to a different program                |
| `max_colors_per_job`                       | Maximum number of distinct colours allowed in one job           |
| `min_cycles_per_job`, `max_cycles_per_job` | Allowed range for the number of cycles in a job                 |

---

## Decision Variables

| Variable                    | Meaning                                                                          |
| --------------------------- | -------------------------------------------------------------------------------- |
| `job_program[i]`            | The production program assigned to job `i` (0 means the slot is unused)          |
| `job_length[i]`             | The number of production cycles in job `i`                                       |
| `job_moulds[i, k, l]`       | Number of moulds of type `k` running colour `l` in job `i` (per cycle)           |
| `total_job_moulds[i, k, l]` | Total units of mould `k` in colour `l` produced by job `i` across all its cycles |
| `job_time[i]`               | Total processing time of job `i`                                                 |
| `job_end[i]`                | Completion time of job `i`                                                       |
| `demand_end[d]`             | Time at which demand `d` is fully satisfied                                      |
| `demand_end_job[d]`         | Index of the job that completes demand `d`                                       |
| `makespan`                  | The time at which all jobs are finished (completion time of the last active job) |
| `waste`                     | Total units produced beyond what is actually required by demands                 |
| `tardiness`                 | Sum over all demands of how late each demand is completed past its due date      |

---

## Constraints

- **Symmetry breaking**: Unused job slots (program = 0) are pushed to the end of the sequence.
- **Slot capacity**: The total number of mould slots used in a job must equal the number of slots defined by the assigned program.
- **Mould availability**: The number of moulds of each type used across a job cannot exceed the number physically available.
- **Colour limit per job**: At most `max_colors_per_job` distinct colour-line combinations can appear in a single job.
- **Demand fulfilment**: For every (mould type, colour) combination with a demand, the cumulative production across all jobs must meet or exceed the total required quantity.
- **Program compatibility**: A mould can only be used in a job that runs the program it is designed for.
- **Colour compatibility**: Certain pairs of colours cannot appear together in the same job.
- **Timing**: Job end times are computed from cycle times and setup times, accounting for whether adjacent jobs use the same program or different programs.
- **Demand timing**: Each demand is assigned to the earliest job after which its cumulative production first reaches the required total.

---

## Objective

Minimise the weighted sum:

$$\text{makespan} + \text{tardiness} + \text{waste}$$

All three components are measured in compatible units and summed directly. A good solution finishes all work quickly, delivers orders on time, and avoids unnecessary overproduction.

## Model update summary

Added concise inline comments in atsp.mzn to clarify:

- core decision variables (`job_program`, `job_length`, mould assignments),
- production/sequence semantics for jobs,
- objective interpretation as makespan + tardiness + waste.
