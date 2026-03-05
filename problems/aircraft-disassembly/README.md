# Aircraft Disassembly Scheduling Model

## Overview

This MiniZinc model addresses the **Aircraft Disassembly Scheduling Problem**, which involves planning the disassembly of an aircraft into its components while optimising resource allocation, skill requirements, and spatial constraints. The goal is to minimise the overall **makespan** (completion time) and associated resource costs.

The model is inspired by:

- CP Optimizer model for Aircraft Disassembly Scheduling ([GitHub link](https://github.com/cftmthomas/AircraftDisassemblyScheduling))
- MiniZinc model for Multi-Skill Project Scheduling Problem ([GitHub link](https://github.com/youngkd/MSPSP-InstLib))

---

## Problem Description

Aircraft disassembly requires:

- **Multiple activities** (e.g., removing wings, engines, avionics).
- **Technicians with specific skills**.
- **Resources** (tools, equipment) that may be unavailable at certain times.
- **Precedence constraints** between tasks (e.g., engine removal before wing removal).
- **Location capacity limits** (e.g., only a certain number of technicians can work in a hangar simultaneously).
- **Mass balance constraints** to maintain structural stability during disassembly.

The challenge is to schedule all activities while respecting these constraints and minimising time and cost.

---

## Key Sets and Parameters

- **ACT**: Set of activities (1..nActs).
- **RESOURCE**: Set of resources (1..nResources).
- **SKILL**: Set of skills (1..nSkills).
- **LOC**: Set of locations (1..nLocations).
- **TIME**: Time horizon (0..maxt).

### Input Data

- `dur[a]`: Duration of activity _a_.
- `sreq[a,s]`: Skill requirement for activity _a_ and skill _s_.
- `mastery[r,s]`: Boolean indicating if resource _r_ has skill _s_.
- `resource_cost[r]`: Cost per time unit for resource _r_.
- `pred[p], succ[p]`: Precedence relationships between activities.
- `loc[a]`: Location of activity _a_.
- `loc_cap[i]`: Capacity of location _i_.
- `occupancy[a]`: Occupancy requirement of activity _a_.
- `unavailable_resource[i], unavailable_start[i], unavailable_end[i]`: Resource unavailability periods.
- `mass[a]`: Mass associated with activity _a_ for balance constraints.

---

## Decision Variables

- `start[a]`: Start time of activity _a_.
- `assign[a,r]`: Boolean indicating if resource _r_ is assigned to activity _a_.
- `contrib[a,r,s]`: Boolean indicating if resource _r_ contributes skill _s_ to activity _a_.
- `overlap[u]`: Boolean for overlapping unrelated activities.
- `act_leq_act[i,j]`: Boolean indicating if activity _i_ starts before or at the same time as activity _j_.

---

## Constraints

1. **Precedence**: Activities must respect given order.
2. **Resource Availability**: Resources cannot work during unavailable periods.
3. **Skill Satisfaction**: Each activity's skill requirements must be met.
4. **Non-Multi-Tasking**: A resource can contribute only one skill per activity.
5. **Skill Mastery**: Resources can only use skills they have mastered.
6. **Location Capacity**: Limit technicians per location using cumulative constraints.
7. **Mass Balance**: Maintain structural stability during disassembly.
8. **Overlap Rules**: Control overlapping of unrelated activities based on resource and skill constraints.

---

## Objective

Minimise:

$$
\text{Objective} = 100000 \times \max(\text{start}) + \sum_{a \in ACT, r \in RESOURCE} (\text{resource\_cost}[r] \times \text{dur}[a] \times \text{assign}[a,r])
$$

This combines:

- **Makespan**: Completion time of the last activity.
- **Resource Cost**: Total cost of assigned resources.

---

## Notes

- The model uses **cumulative** and **disjunctive** global constraints for resource and location management.
- Mass balance constraints ensure safe disassembly by limiting imbalance at any point.
- If any parameter (e.g., mass balance sets) is unclear, consult domain experts for clarification.

---

### References

- [Aircraft Disassembly Scheduling CP Model](https://github.com/cftmthomas/AircraftDisassemblyScheduling)
