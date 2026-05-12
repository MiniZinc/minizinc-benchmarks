# Soccer Computational Problem

This MiniZinc model studies a **soccer league ranking question**: given the current points of all teams, the remaining matches, and some requested ranking conditions, is there a way to assign results to the remaining games so that the final table is consistent with those conditions?

In the model, each remaining game can end in one of the usual point patterns:

- win/loss: 3 points to one team and 0 to the other
- draw: 1 point to each team

So the model is not optimizing anything. It is a **satisfaction problem**: it only asks whether at least one feasible completion of the season exists.

## Inputs

The main input data are:

- `n`: number of teams
- `iPoints[i]`: current points of team `i`
- `games[g,1]`, `games[g,2]`: the two teams involved in remaining game `g`
- `positionConstraints`: ranking requirements that some teams must satisfy

The exact encoding of `positionConstraints` is not documented inside the model, but from the constraints it appears to represent statements such as:

- team `t` finishes exactly in position `p`
- team `t` finishes above / at least / below / at most some position `p`

That interpretation is inferred from the arithmetic conditions in the model, so there is a small amount of uncertainty here.

## Decision variables

The model chooses:

- `points[g,1..2]`: the points awarded to the two teams in each remaining game
- `fPoints[i]`: final points of team `i`
- `finalPosition[i]`: final league position assigned to team `i`
- `bestPosition[i]`: best rank team `i` could occupy given ties on points
- `worstPosition[i]`: worst rank team `i` could occupy given ties on points

The `bestPosition` / `worstPosition` pair is the key modeling idea. Since teams can finish tied on points, the model first computes the interval of possible ranks implied by total points alone, then chooses one distinct `finalPosition` for each team inside that interval.

## Core constraints

1. **Valid match outcomes.** For each remaining game, the two awarded point values must sum to 2 or 3, which leaves only `(1,1)`, `(3,0)`, or `(0,3)`.
2. **Final points calculation.** Each team’s final score equals its current points plus the points it receives from all remaining matches.
3. **Ranking bounds from points.**
   - `worstPosition[i]` counts teams with points greater than or equal to team `i`
   - `bestPosition[i]` removes the effect of equal-point teams
4. **Chosen final positions.** `finalPosition[i]` must lie between the best and worst possible rank for team `i`.
5. **No duplicate positions.** All final positions must be different.
6. **Requested ranking conditions.** The encoded `positionConstraints` are enforced for selected teams.

## Objective

There is **no objective function**. The solve item is `satisfy`, so any feasible season completion is an acceptable solution.

## Output

A solution reports:

- the points assigned in each remaining game
- each team’s final points
- each team’s chosen final position
- each team’s best and worst possible position under point ties

## Notes for beginners

This is a good example of turning a sports-table question into constraints:

- first model legal match results
- then compute season totals
- then derive ranking information from those totals
- finally enforce the scenario you care about

One subtle point is that the model does **not** encode real soccer tie-breakers such as goal difference. Ties on points are handled only through admissible rank intervals (`bestPosition` to `worstPosition`).

## References

Identifiable sources from the repository:

- Model title in the file header: **“Soccer Computational Problem (Position in Ranking Problem)”**
- Submitted by Robinson Duque, Alejandro Arbelaez, and Juan Francisco Díaz
- Included in MiniZinc Challenge benchmark metadata for 2018 and 2020

The model header also says “See README file for a detail description”, but that original source README is not present here, so this summary is based on the MiniZinc model itself and the accompanying metadata.

## Model update summary

Added concise inline comments in ecp.mzn to clarify:

- match-result and final-position decision variable semantics,
- rank-interval and position-constraint feasibility interpretation,
- satisfaction-only solve intent for standings scenarios.
