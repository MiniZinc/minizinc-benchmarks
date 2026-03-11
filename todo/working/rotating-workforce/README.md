# Rotating Workforce Scheduling

## Problem Description

Imagine a hospital, factory, or transport system that needs staff around the clock, every day of the week. You have a fixed pool of workers and a set of named shift types (e.g. morning, afternoon, night). The goal is to build a single **cyclic schedule** such that:

- Every worker follows **exactly the same weekly pattern** of shifts and rest days — they just start the cycle at a different offset. This is the "rotating" property that gives the problem its name.
- On each day of the week, every shift type is covered by **exactly the required number of workers**.
- Consecutive working days are kept within allowed limits: there is a minimum and maximum number of **days on duty** in a row.
- Rest periods also form contiguous blocks within allowed minimum and maximum **days-off** lengths.
- Certain consecutive shift pairs are **forbidden** (e.g. a night shift must not be immediately followed by a morning shift), optionally even when a days-off block separates them.

Because all workers share the same rotating pattern, finding one valid sequence effectively determines the full roster for everyone.

## Parameters (Inputs)

| Parameter                     | Meaning                                                       |
| ----------------------------- | ------------------------------------------------------------- |
| `week_length`                 | Number of days in one rotation cycle                          |
| `nb_workers`                  | Total number of workers                                       |
| `nb_shifts`                   | Number of different shift types (not counting days off)       |
| `shift_name`                  | Human-readable label for each shift                           |
| `shift_block_min/max[s]`      | Min/max consecutive days a worker may work the same shift `s` |
| `min_work` / `max_work`       | Min/max total consecutive on-duty days in a row               |
| `min_daysoff` / `max_daysoff` | Min/max consecutive days off in a rest block                  |
| `temp_req[s, d]`              | How many workers must be on shift `s` on day `d`              |
| `forbidden_before/after`      | Pairs of shifts that must not appear consecutively            |

## Decision Variables

The core decision is the 2-D array **`plan[w, d]`**, where:

- `w` ranges over `1..nb_workers` (think of it as the worker's offset into the rotation, or equivalently the week row in the cyclic schedule).
- `d` ranges over `1..week_length` (day within the cycle).
- Each cell holds a shift identifier from `SHIFT`, or the special constant `OFF` (rest day).

Reading row `w` of `plan` gives the complete day-by-day assignment for the worker who starts the rotation `w` positions in. Because the schedule is cyclic, all workers share this same pattern.

Two auxiliary arrays — `plan_sort` (a solver-friendly reordering of `plan`) and `dplan` (a flattened 1-D version) — are defined via constraints and carry no additional information; they are technical devices to make the model easier for the solver to handle.

## Constraints

1. **Coverage** — On every day `d`, the number of workers assigned to each shift must equal `temp_req[s, d]` exactly. The `global_cardinality_low_up` global constraint enforces this.

2. **Sequence legality** — A pre-computed deterministic finite automaton (DFA) is applied to the one-dimensional schedule sequence via the `regular` global constraint. The DFA encodes all block-length limits (on-duty minimum/maximum, days-off minimum/maximum, per-shift consecutive limits) and all forbidden shift-to-shift transitions in one pass.

3. **Cyclic wrap-around** — The first row of `plan` and an appended "extra" row `nb_workers + 1` are forced to be identical, so the schedule connects cleanly at the boundary of the cycle.

4. **Redundant counting** — A set of propagation-helping constraints tracks how many on-duty and off-duty days remain after each week and checks that the remaining counts can still be packed into legal blocks. These constraints do not change the set of solutions but help the solver prune dead ends faster.

5. **Symmetry breaking** — A rest day is fixed at the very end of the schedule (and an on-duty day at the start when the staffing levels permit), reducing the number of equivalent solutions the solver explores.

## Objective

This is a pure **satisfaction** problem. There is no cost function to minimise or maximise — the solver simply looks for _any_ assignment of `plan` that meets all of the constraints above (`solve satisfy`).

## Notes and Uncertainty

- The model requires `min_daysoff ≤ 2`; if a data file passes a larger value the model fails at runtime with an assertion error. This is a documented limitation of the DFA construction.
- The shift ordering used inside the solver (`shift_sort = sort_none`) can be overridden by individual data files to influence how branches are explored; the default leaves the order unchanged.
- The actual instance data (staffing numbers, shift definitions, forbidden pairs, etc.) lives in separate `.dzn` files in the `data/` subdirectory and is not bundled in the model file. You must supply a data file when running the model.
- Some combinations of block-length parameters produce no feasible schedule (the feasibility cross-checks at the top of the model will report `UNSATISFIABLE`); this is expected behavior, not a model bug.

## Reference

Nysret Musliu, Andreas Schutt, Peter J. Stuckey (2018).  
**"Solver Independent Rotating Workforce Scheduling."**  
_Integration of Constraint Programming, Artificial Intelligence, and Operations Research (CPAIOR 2018)_, LNCS 10848, pp. 429–445.  
<https://link.springer.com/chapter/10.1007/978-3-319-93031-2_31>
