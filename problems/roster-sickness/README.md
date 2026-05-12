# Roster Re-Planning with Sickness (MiniZinc, Beginner-Friendly)

## What problem does this model solve?

This model repairs an employee roster after disruptions (for example, sickness-related absences) while trying to keep service coverage high and workload fair.

You start from an existing plan `is_assigned[e,s]` (employee `e` originally on shift `s`) and decide a new plan `assigned[e,s]`.

In plain terms, the model tries to:

- keep valid existing assignments,
- avoid illegal assignments (wrong expertise or time overlap),
- fill as many shifts as possible,
- and keep each employee close to their contract hours.

## Main data (inputs)

- `n_shifts`, `n_employees`, `n_expertises`: problem sizes.
- `contract[e]`: contracted work time for employee `e`.
- `employee_expertises[e]`: skills/expertises employee `e` has.
- `req_expertise[s]`: expertise required by shift `s`.
- `start_time[s]`, `stop_time[s]`: shift time window.
- `is_assigned[e,s]`: original roster assignment matrix.

The model also checks that shift start times are sorted.

## Decision variables

- `assigned[e,s]` (bool): whether employee `e` is assigned to shift `s` in the repaired roster.
- `contract_diff[e]`: worked time minus contracted time for employee `e`.
- `number_assigned_shifts`: total number of filled shifts.
- `summed_abs_contract_diff`: total absolute contract deviation across employees.

## Core constraints (how feasibility is enforced)

- **Keep existing assignments:** if `is_assigned[e,s]` is true, then `assigned[e,s]` must also be true.
- **At most one employee per shift:** no double staffing of a single shift.
- **No overlapping shifts per employee:** an employee cannot be assigned to overlapping time intervals.
- **Skill matching:** an employee can only work shifts requiring an expertise they have.
- **Respect incumbent ownership logic:** if a shift is already assigned to someone else in the original plan, other employees are blocked from taking it.

## Objective

Yes, this model has an objective. It maximizes:

`objective = W * number_assigned_shifts - summed_abs_contract_diff`

where `W` is chosen large enough to make the optimization lexicographic-like:

1. prioritize filling as many shifts as possible,
2. then reduce contract-hour unfairness.

## Uncertainty and modeling assumptions

- The file name and context suggest sickness handling, but there is no explicit variable like `is_sick[e]`; sickness appears to be represented indirectly through the given input matrix `is_assigned` and reassignment restrictions.
- The model contains both a pairwise overlap rule and a stronger overlap-aggregation rule; this may reflect robustness/redundancy choices from competition tuning.
- `time_units_per_hour` is provided but not directly used in this model file, so unit interpretation depends on the data convention.

## References (identifiable from repository)

- Model file: `todo/working/roster-sickness/bool-model-sickness.mzn`.
- Metadata indicates inclusion in **MiniZinc Challenge 2022** benchmark set: `todo/working/roster-sickness/metadata.json`.
- Header comments mention modifications by **MiniZinc Challenge Organisers**.

## Model update summary

Added concise inline comments in bool-model-sickness.mzn to clarify:

- reassignment and contract-difference decision variable semantics,
- overlap/qualification feasibility interpretation under preserved assignments,
- lexicographic-style maximization intent for coverage and balance.
