# Test Scheduling (Beginner-Friendly Explanation)

This model schedules a set of tests so that all tests finish as early as possible.

In plain words:
- Each test has a fixed duration.
- Each test can run only on certain machines.
- Some tests use shared resources (like equipment), and tests that need the same resource cannot run at the same time.
- We want to **minimize the makespan** (the finishing time of the last test).

---

## What the model takes as input

The model defines:
- `Machines`: available machines.
- `Resources`: shared resources.
- `capacity[r]`: capacity per resource (currently treated as 1 in the active constraint).
- `nTests`, with tests indexed as `1..nTests`.
- `duration[t]`: how long test `t` runs.
- `possibleMachines[t]`: machines that can execute test `t`.
- `usedResources[t]`: resources required by test `t`.

It also computes rough bounds for the makespan:
- `minMakespan`: lower bound from resource-based workload.
- `maxMakespan`: upper bound from machine-based workload.

---

## Decision variables

The solver must choose:
- `usesMachine[t]`: which machine each test runs on.
- `startTime[t]`: when each test starts.
- `objective`: the makespan (end time of the latest-finishing test).

---

## Core constraints

1. **Machine eligibility**  
   Every test must be assigned to one of its allowed machines.

2. **No machine overlap**  
   On each machine, two tests cannot run simultaneously.

3. **No resource conflict**  
   For each resource, tests using that resource are forced not to overlap in time.

4. **Symmetry breaking**  
   For machines that are effectively interchangeable, an ordering rule is added to reduce equivalent duplicate solutions and speed solving.

5. **Makespan definition and anchoring**  
   - `objective` is constrained to the maximum of `startTime[t] + duration[t]` over all tests.
   - A redundant constraint `min(startTime) = 0` anchors the schedule so time is not shifted unnecessarily.

---

## Objective

The model solves:
- **minimize `objective`** (minimize total completion time / makespan).

---

## Notes on uncertainty and interpretation

- The file includes `capacity[r]`, but the active resource constraint uses `disjunctive(...)`, which enforces one-at-a-time use for each resource. A commented line suggests a more general `cumulative(..., capacity[r])` formulation. So this model appears specialized to instances where resource capacity is effectively 1.
- The model defines both `minMakespan` and `maxMakespan`; these are used as bounds and may be conservative depending on instance structure.
- Search annotations are present in the `solve` item, but they are solver-guidance details rather than core problem definition.

---

## Identifiable references

- Model header comment: **“Model for Test Scheduling Problem (CSPlib problem 073)”**.
- Model attribution in file header: **Gustav Björdal (2018-05-17)**.
- Folder metadata (`metadata.json`) indicates this benchmark appears in challenge sets for **2018** and **2023**.
