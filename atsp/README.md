# Artificial Teeth Scheduling Problem Instances for MiniZinc Challenge 2021:

The model is taken from the ICAPS 2021 paper:
"Automated Production Scheduling for Artificial Teeth Manufacturing" from Winter et al.
https://ojs.aaai.org/index.php/ICAPS/article/view/15997

== Main Model File ==
atsp.mzn

Instances are based on real-life instances (but slightly shrinked so that they are not too challenging for exact solvers)

Contact:
winter@dbai.tuwien.ac.at
https://dbai.tuwien.ac.at/staff/winter/

# Automatically generated description

## Overview

This MiniZinc model addresses a **complex job scheduling problem** involving multiple production lines, moulds, colours, and customer demands. The goal is to assign jobs to programmes and moulds while respecting resource constraints, colour compatibility, and due dates. The objective is to minimise a combined measure of **makespan**, **waste**, and **tardiness**.

This type of problem is common in manufacturing environments where products require different moulds and colours, and production must be scheduled efficiently to meet customer demand.

---

## Problem Description

We have:

- A set of **jobs** to schedule.
- Each job uses a **programme** (a configuration for moulds and colours).
- Jobs consist of multiple **cycles**, and each cycle produces items using moulds and colours.
- Customer **demands** specify required quantities, colours, and due dates.
- There are **setup times** between jobs, which depend on whether the programme changes.
- Constraints ensure mould availability, colour compatibility, and demand fulfilment.

The challenge is to:

- Assign jobs to programmes and moulds.
- Determine job lengths (number of cycles).
- Sequence jobs to minimise overall production time and penalties.

---

## Key Sets and Parameters

- **jobs**: 1..max_jobs — Jobs to schedule.
- **programs**: 1..num_programs — Available programmes.
- **moulds**: 1..num_moulds — Types of moulds.
- **colors**: 1..num_colors — Available colours.
- **demands**: 1..num_demands — Customer demands.
- **lines**: 1..num_lines — Production lines.

### Important Inputs

- `slots_per_program[p]`: Number of mould slots in programme _p_.
- `cycle_time_for_program[p]`: Cycle time for programme _p_.
- `available_moulds[m]`: Quantity of mould _m_ available.
- `demand_qty[d]`: Quantity required for demand _d_.
- `demand_duedate[d]`: Due date for demand _d_.
- `color_compatibility[c1,c2]`: Whether colours _c1_ and _c2_ can be used together.

---

## Decision Variables

- `job_program[i]`: Programme assigned to job _i_ (0 if unused).
- `job_length[i]`: Number of cycles for job _i_.
- `job_moulds[i,m,c]`: Number of moulds of type _m_ and colour _c_ in job _i_.
- `total_job_moulds[i,m,c]`: Total production for mould _m_ and colour _c_ in job _i_.
- `job_end[i]`: Completion time of job _i_.
- `makespan`: Overall completion time.
- `waste`: Excess production beyond demand.
- `tardiness`: Sum of delays beyond due dates.

---

## Constraints

1. **Symmetry Breaking**: Jobs after an unused job must also be unused.
2. **Mould Allocation**: Total moulds per job match programme slots.
3. **Availability**: Mould usage does not exceed available quantities.
4. **Colour Limits**: Jobs cannot exceed maximum allowed colours.
5. **Demand Fulfilment**: Production meets or exceeds demand quantities.
6. **Programme Compatibility**: Moulds must match assigned programme.
7. **Colour Compatibility**: Incompatible colours cannot appear in the same job.
8. **Timing**:
   - Job times depend on cycles and programme cycle time.
   - Job end times include setup times.
   - Demand completion times depend on job sequence.

---

## Objective

Minimise:

$$
\text{Objective} = \text{makespan} + \text{tardiness} + \text{waste}
$$

Where:

- **Makespan** = Maximum job end time.
- **Tardiness** = Sum of lateness beyond due dates.
- **Waste** = Excess production beyond demand.

---

## Notes

- This model combines **job sequencing**, **resource allocation**, and **demand satisfaction**.
- It is suitable for industries with complex setups, such as injection moulding or multi-colour printing.
- If any parameter (e.g., colour compatibility rules) is unclear, consult domain experts.

---
