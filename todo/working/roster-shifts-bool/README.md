# Roster Shifts (Boolean Model) — Beginner-Friendly Explanation

## What problem is this model solving?

This MiniZinc model builds a **staff roster**: it decides which employee should cover which shift.

Each shift has:

- a start and stop time,
- a required expertise (skill).

Each employee has:

- a contract amount (target workload),
- a set of expertises they are qualified for.

The model tries to assign shifts so that:

1. shifts are covered as much as possible,
2. employees are not assigned to overlapping shifts,
3. employees only get shifts they are qualified for,
4. workloads stay reasonably close to their contracts.

---

## Main decision variables

- `assigned[e, s]` (boolean):
  - `true` if employee `e` is assigned to shift `s`, otherwise `false`.

- `contract_diff[e]` (integer):
  - actual assigned work time for employee `e` minus `contract[e]`.
  - positive means over contract, negative means under contract.

Derived summary variables:

- `number_assigned_shifts`: total count of assigned employee-shift pairs.
- `summed_abs_contract_diff`: total imbalance from contracts, using absolute values.
- `objective`: combined score used for optimization.

---

## Core constraints (rules)

1. **At most one employee per shift**
   - For every shift, the sum of assignments over employees is `<= 1`.

2. **No overlapping shifts for the same employee**
   - If two shifts overlap in time, an employee cannot be assigned to both.

3. **Skill compatibility**
   - If an employee lacks the expertise required by a shift, assignment is forbidden.

4. **Upper bound on overtime vs contract**
   - For employees with positive contract time, assigned time must be at most **130%** of contract.

5. **Input validation**
   - Start times must already be sorted (`assert(start_time=sort(start_time), ...)`).

6. **Symmetry breaking (performance aid)**
   - For identical shifts, an ordering rule is added to reduce equivalent duplicate solutions.

---

## Objective (what is optimized)

The model **maximizes**:

`objective = W * number_assigned_shifts - summed_abs_contract_diff`

where `W` is chosen large enough to make this effectively lexicographic:

- First priority: maximize number of assigned shifts.
- Second priority: among those, minimize total contract imbalance.

So the solver prefers covering more shifts, then improving fairness/workload matching.

---

## Notes about search strategy

The model file contains a boolean search annotation (`bool_search(...)`) and uses `solve :: search maximize objective`.
This README intentionally does **not** analyze search heuristics in depth, and focuses on problem structure and optimization meaning.

---

## Uncertainty / caveats

- `<= 1` employee per shift means shifts may remain unfilled; this is a modeling choice and may or may not match real staffing requirements.
- Contract balancing is based on **shift durations** (`stop_time - start_time`) in model time units; interpretation depends on data quality and `time_units_per_hour`.
- A commented-out “redundant” overlap constraint is marked as incorrect by challenge organizers and is disabled.
- Without seeing the `.dzn` data, we cannot confirm whether all business rules (breaks, legal rest times, minimum coverage, etc.) are represented.

---

## Identifiable references in the model

From this file alone, explicit references are limited to:

- `sort.mzn` (MiniZinc standard library include for sorting),
- comment: “Changes by the MiniZinc Challenge Organisers” indicating a disabled incorrect constraint.

No external paper, URL, or original problem citation is explicitly included in `bool-model.mzn`.
