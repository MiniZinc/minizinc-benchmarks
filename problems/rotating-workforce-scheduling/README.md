# Rotating Workforce Scheduling

## Problem Description

A company needs to staff a workplace around the clock, every day of the week.
Each day has a fixed number of workers required on each of three shifts: **Day**, **Evening**, and **Night**.
Employees who are not working on a given day are simply marked as **Off**.

The twist is that the schedule is _rotating_: every employee follows the same weekly pattern, but each employee starts at a different point in the cycle.
Concretely, if there are `N` employees then the cycle length is `N` weeks, and employee `k` works the pattern that week `k` defines.
This means designing the schedule for one complete cycle automatically produces a fair, repeating rota for all staff.

The goal is to find _any_ valid schedule that satisfies all staffing requirements and labour rules — this is a **satisfaction** problem with no objective to minimise or maximise.

## Parameters

| Parameter                  | Meaning                                                              |
| -------------------------- | -------------------------------------------------------------------- |
| `employees`                | Number of employees (also the number of weeks in one rotation cycle) |
| `requirements[day, shift]` | Exact number of workers required on each day/shift combination       |

## Decision Variables

| Variable              | Domain                       | Meaning                                                                                           |
| --------------------- | ---------------------------- | ------------------------------------------------------------------------------------------------- |
| `schedule[week, day]` | `{Off, Day, Evening, Night}` | The shift assigned to the employee in position `week` on each `day` of their week in the rotation |

A helper array `repeated_schedule` appends the first two weeks of the schedule to the end of the cycle so that constraints can look across week boundaries without special casing.

## Constraints

1. **Coverage** — For every day of the week, exactly the required number of employees work each shift type (`global_cardinality_low_up`).

2. **Two consecutive days off per week** — Every employee must have at least two _consecutive_ rest days somewhere in their week. This is enforced with a `regular` constraint and the pattern `".* Off Off .*"`.

3. **No more than five consecutive working days** — Looking across week boundaries, no run of six consecutive days may be entirely work days (`sliding_sum` over the repeated schedule).

4. **Weekend rest** — At least one out of every three consecutive weekends (Saturday + Sunday) must be fully off (`sliding_sum` over a Boolean weekend-free indicator).

5. **Night-shift limit** — No employee may work more than two night shifts in a row; after any night shift block, a rest day is required before any other work. This is modelled as a finite automaton with five states using the `regular` constraint.

## No Objective Function

This model is a pure **feasibility** problem. The solver simply searches for a schedule that satisfies all constraints. All generated instances are known to have at least one solution.

## Notes and Uncertainty

- The model is loosely based on the formulation in the reference below, but the specific constraints are inspired by **Swedish labour regulations** and therefore differ from the original paper's rule set.
- The search annotation was modified by the MiniZinc Challenge organisers (changed from `dom_w_deg` to `input_order`), which may affect solver performance compared to the original.
- Instance generation details are not included in the model file; the exact distribution of `requirements` values across instances is unknown.

## References

- Nysret Musliu, Andreas Schutt, and Peter J. Stuckey. _The Rotating Workforce Scheduling Problem_. In Proceedings of the 17th International Conference on Principles and Practice of Constraint Programming (CP 2011), Lecture Notes in Computer Science, Springer, 2011.
- Model copyright © 2022 Mikael Zayenz Lagerkvist (MIT License).
