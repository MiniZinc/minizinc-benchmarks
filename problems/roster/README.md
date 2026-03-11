# Roster (MiniZinc) — Beginner-Friendly Explanation

## What problem is this model solving?

This model builds a **staff roster over several weeks**.  
Each day needs a required number of workers on each shift type, and each worker (one per week-row) must follow work/rest pattern rules.

The shift codes are:

- `1 = Rest`
- `2 = Morning`
- `3 = Day`
- `4 = Evening`
- `5 = Joker` (an extra shift category used in demand matching)

The goal is to satisfy all hard rules and make the schedule as “good” as possible under two soft penalties.

## Inputs

- `weeks`: number of weeks to schedule.
- `reqt[shift, day]`: required count for each shift type (`1..5`) on each weekday (`1..7`).
- `minobj`: lower bound used for the objective variable domain.

Derived value:

- `flatsize = 7 * weeks` (total number of day-slots in one worker line across all weeks).

## Decision variables

- `roster[week, day] in 1..5`: assigned shift code for each week/day position.
- `flatroster[1..flatsize]`: same assignments as `roster`, but flattened to one dimension.
- `longflatroster[1..flatsize+6]`: extended version used for wrap-around windows across week boundaries.
- Penalty counters:
  - `evemorn`: number of Evening→Morning transitions.
  - `isolated`: number of isolated Rest days.
- `objective = evemorn + isolated`.

## Hard constraints (must always hold)

1. **Linking arrays**: `roster` and `flatroster` represent exactly the same assignments.
2. **Demand satisfaction**: for each day and shift type, the number of workers assigned that shift equals `reqt`.
3. **At least one rest in any 7-day window**: avoids long continuous work stretches.
4. **No 4 rests in any 4-day window** (implemented via `at_most(3, ..., Rest)`): limits excessive consecutive rest.
5. **Wrap-around handling**: tail positions in `longflatroster` repeat the start of `flatroster` so window constraints also apply across the end/start boundary.

## Soft constraints and objective

The model allows two undesirable patterns but penalizes them:

- **Evening followed by Morning** (`evemorn`): each occurrence adds 1.
- **Isolated Rest day** (`isolated`): a Rest day whose neighbors are both non-Rest adds 1.

It then **minimizes**:

`objective = evemorn + isolated`

So the solver looks for feasible rosters with the smallest total penalty.

## Output

The model prints:

- the roster matrix,
- `evemorn`,
- `isolated`,
- `objective`,
- and a simple week/day formatted view.

## Notes on uncertainty / interpretation

- The role of `Joker` is not explicitly described beyond being a fifth shift category used in requirements.
- Comments include a heading “No sequence of three Rest days,” but the implemented rule is `at_most(3)` over a 4-day window, which forbids **four** Rest days in that window (not three).
- `minobj` is declared as input and used only as a lower bound for `objective`; expected values/rationale depend on the accompanying data file.

## Identifiable references

- In-file comments indicate this is an example solution for **FIT3022 Assignment 1** (dated 6 May 2008).
- In-file note mentions a **2009 MiniZinc Challenge** formulation in `roster_model.old`.
- Uses global predicates from MiniZinc’s `globals.mzn` (`exactly`, `at_least`, `at_most`).
