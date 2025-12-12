# EchoSched: Energy-Aware Job Scheduling Model

## Overview

This MiniZinc model addresses an **energy-aware job scheduling problem** on multiple machines. Each job consists of tasks that must be processed on different machines in a specific order. The processing time and energy consumption of each task depend on the chosen speed setting for that machine. The goal is to schedule all tasks while minimising a combined measure of **makespan** (total completion time) and **energy consumption**.

---

## Problem Description

We have:

- A set of **jobs** (`JOBS`), each requiring processing on multiple machines.
- A set of **machines** (`MACHINES`).
- Each machine can operate at different **speed levels** (`SPEED`), affecting both processing time and energy usage.
- **Precedence constraints** define the order in which tasks for the same job must be executed across machines.

The challenge is to:

- Assign start times and speed settings for each job-machine pair.
- Ensure tasks respect precedence and do not overlap on the same machine.
- Minimise the combined cost of makespan and energy consumption.

---

## Key Sets and Parameters

- `JOBS`: Set of jobs.
- `MACHINES`: Set of machines.
- `SPEED`: Number of available speed levels.
- `time[j,m,s]`: Processing time for job `j` on machine `m` at speed `s`.
- `energy[j,m,s]`: Energy consumed for job `j` on machine `m` at speed `s`.
- `precedence[j,m]`: Order index for job `j` on machine `m`.

---

## Decision Variables

- `start_time[j,m]`: Start time of job `j` on machine `m`.
- `SpeedScaling[j,m]`: Speed level chosen for job `j` on machine `m`.
- `makespan`: Maximum completion time across all jobs and machines.
- `consumedEnergy`: Total energy consumed by all jobs.
- `objective`: Combined measure of makespan and energy consumption.

---

## Constraints

1. **Precedence**:
   - For each job, tasks must follow the specified order across machines.
2. **Non-Overlap**:
   - No two jobs can run simultaneously on the same machine.
3. **Completion Time**:
   - Makespan is the maximum finish time of all tasks.

---

## Objective

Minimise:

$$
\text{objective} = \text{makespan} + \text{consumedEnergy}
$$

This balances fast completion with energy efficiency.

---

## Notes

- The model supports multiple speed levels, allowing trade-offs between time and energy.
- Suitable for manufacturing, cloud computing, and energy-aware scheduling applications.
- If precedence or speed settings are unclear, consult domain-specific requirements.

---
