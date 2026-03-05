# Flowshop Scheduling with Workers

## Overview

This MiniZinc model addresses a **flowshop scheduling problem with worker assignments**. The goal is to schedule the production of multiple products across a series of stations, considering manual and automatic work steps, worker movement times, and release times. The objective is to minimise the overall completion time (makespan).

---

## Problem Description

In a flowshop environment:

- Products move through stations in a fixed order.
- Each station may require one or two work steps:
  - **Manual steps** (setup and takedown) performed by workers.
  - **Automatic steps** performed by machines.
- Workers must move between stations, which incurs walking time.
- Products and workers have release times before they can start work.
- Buffers between stations limit how many products can wait.

The challenge is to assign start times for all work steps and allocate workers efficiently while respecting precedence and resource constraints.

---

## Key Parameters

- `horizon`: Maximum time horizon for scheduling.
- `numberWorkers`: Total number of workers available.
- `numberStations`: Number of stations in the flowshop.
- `numberProducts`: Number of products to process.
- `numberProductTypes`: Different product types.
- `numberWorksteps`: Fixed at 2 (setup and takedown).
- `currentStation`, `currentStep`, `currentBuffer`: Current position and state of each product.
- `releaseTime`: Time when each product becomes available.
- `workerInitial`: Initial station for each worker.
- `releaseTimeW`: Time when each worker becomes available.
- `numberManualWorksteps`: Indicates if a station requires manual steps (1 or 2).
- `setupTimes`, `takedownTimes`: Times for manual steps.
- `workerMovementMatrix`: Time for a worker to move between stations.
- `productionTimeMatrix`: Automatic processing times.
- `productType`: Type of each product.

---

## Decision Variables

- `proST[product, station, workstep]`: Start time of a product's work step at a station.
- `proD[product, station, workstep]`: Duration of the work step.
- `workST[product, station, workstep, worker]`: Start time if a worker performs the step.
- `workD[product, station, workstep, worker]`: Duration for a worker's step.
- `objective`: Completion time of the last product at the last station.

---

## Constraints

1. **Workstep Allocation**:
   - Each work step is performed by exactly one worker if manual.
   - Automatic steps occur without worker assignment.
2. **Precedence**:
   - Products must follow station order.
   - Stations process products in queue order.
3. **Buffer Limits**:
   - At most one product can occupy a buffer between stations.
4. **Worker Movement**:
   - Workers need walking time between tasks.
   - Initial positions and release times are respected.
5. **Release Times**:
   - Products and workers cannot start before their release times.
6. **Automatic Station Rules**:
   - Automatic steps occur after setup with a fixed delay.
7. **Symmetry Breaking**:
   - Reduces redundant solutions for efficiency.

---

## Objective

Minimise:
\[
\text{objective} = \text{completion time of the last product at the last station}
\]
This represents the **makespan** of the schedule.

---

## Notes

- The model uses **interval variables** and alternative constraints to link product steps and worker assignments.
- Suitable for complex manufacturing environments where human and machine tasks interact.
- Can be extended to include energy costs or worker skill levels.
