# The Work Task Variation Problem

This repository contains a MiniZinc model and a set of generated
insances for the Work Task Variation problem.

# Automatically generated description

# Work Task Variation Model

## **Overview**

This MiniZinc model addresses the **Work Task Variation problem**, which involves scheduling activities for multiple resources over a series of time slots. The aim is to create a valid schedule that satisfies resource requirements and fixed assignments while minimising the overall cost associated with task runs and frequency of activities.

---

## **Problem Description**

The problem consists of:

- A set of **resources** (e.g., workers or machines).
- A set of **activities** that can be assigned to resources.
- A fixed number of **time slots** during which activities occur.
- **Requirements** specifying how many resources should perform each activity in each time slot.
- Optional **fixed assignments** where certain resources must perform specific activities at given slots.

The schedule must:

- Respect activity requirements for each time slot.
- Honour fixed assignments.
- Ensure that activities for each resource are grouped into runs (continuous periods of the same activity) and surrounded by idle periods (`None`).

The objective is to minimise the total cost, which includes:

- **Run costs**: Based on the length of each continuous run of an activity.
- **Frequency costs**: Based on how many times an activity is started by a resource.

---

## **Key Inputs**

- `Resources`: Set of resources to schedule.
- `Activities`: Set of activities.
- `slots`: Number of time slots.
- `requirements[a, s]`: Number of resources required for activity `a` in slot `s`.
- `fixed[r, s]`: Optional fixed activity for resource `r` at slot `s`.
- `activity_run_cost[a, l]`: Cost for a run of activity `a` of length `l`.
- `activity_frequency_cost[a, f]`: Cost for `f` runs of activity `a`.

---

## **Decision Variables**

- `schedule[r, s]`: Activity assigned to resource `r` at slot `s` (or `None` if idle).
- `run_end[r, s]`: Boolean indicating if a run ends at slot `s`.
- `run_length[r, s]`: Length of the current run for resource `r` up to slot `s`.
- `run_cost[r, s]`: Cost incurred when a run ends at slot `s`.
- `frequency_cost[r, a]`: Cost for the number of runs of activity `a` for resource `r`.
- `objective`: Total cost (sum of run costs and frequency costs).

---

## **Constraints**

1. **Activity Structure:**  
   Each resource's schedule must consist of runs of activities surrounded by idle periods (`None`).
2. **Slot Requirements:**  
   For each time slot, the number of resources assigned to each activity must match the specified requirements.
3. **Fixed Assignments:**  
   If a fixed activity is specified for a resource at a slot, it must be respected.
4. **Run Management:**
   - Detect run ends and calculate run lengths.
   - Compute run costs based on activity and run length.
5. **Frequency Costs:**  
   Count the number of runs for each activity per resource and apply frequency cost.

---

## **Objective**

Minimise:

```minizinc
objective = sum(run_cost) + sum(frequency_cost);
```

This ensures the schedule is cost-efficient while meeting all requirements.

---

## **Applications**

- Workforce scheduling with cost considerations.
- Machine task allocation in manufacturing.
- Any scenario requiring balanced activity distribution and minimisation of operational costs.

---
