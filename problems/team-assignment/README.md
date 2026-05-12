# Team Assignment (MiniZinc model explained)

## What problem is this model solving?
This model assigns players to teams for a multi-board setting (for example, a board game league where each team has one player per board position).

It tries to balance **two goals**:
1. Keep teams close in total strength (fair competition).
2. Satisfy requests that certain players should be on the same team.

So the model is a **constrained optimization** problem: all assignment rules must be respected, and among valid assignments it chooses the best score.

## Inputs (data the model expects)
- `boards`: number of board positions in each team.
- `teams`: number of teams.
- `players`: number of players.
- `Rating[p]`: strength/rating of each player.
- `Board[p]`: board index for each player (declared in the model, but not actively used in constraints).
- Request data:
  - `SingleRequested`: pairs of players whose co-assignment gives 1 point.
  - `DoubleRequested`: pairs of players whose co-assignment gives 2 points.
  - Counts such as `requests`, `singleRequests`, `doubleRequests`.

## Decision variables
- `Team[p]`: which team player `p` is assigned to (`1..teams`).
- `TeamRating[t]`: total rating of team `t` (computed using `bin_packing_load`).
- `balance`: difference between strongest and weakest team by total rating.
- `happiness`: weighted number of satisfied player-pair requests.
- `objective`: final score to maximize.

## Core constraints (plain-language)
1. **One player per team per board slot**  
   For each board group, the assigned team numbers must all be different (`alldifferent`).
2. **Equal team sizes**  
   A bin-packing constraint with unit item sizes ensures each team gets exactly `boards` players.
3. **Symmetry breaking**  
   The first `teams` players are fixed to different teams (`Team[t] = t`) to reduce equivalent duplicate solutions.

## Objective
The model maximizes:

`objective = 1000 * happiness - balance`

Interpretation:
- Increasing `happiness` is strongly prioritized (weight 1000).
- For equal happiness, lower `balance` is preferred (more even team strength).

## Output
The model prints:
- the full team assignment array (`Team`),
- and the final objective value.

## Uncertainty / assumptions to keep in mind
- The exact real-world meaning of `Board[p]` is not fully clear from this file alone; it is declared but not used directly in constraints.
- The model assumes player ordering is meaningful (board groups are derived from index ranges like `(b-1)*teams + t`).
- Request semantics are inferred from variable names and objective terms (same-team preference scoring).

## References
- Model header indicates: **Optimal Team Assignment**, submitted to the **MiniZinc Challenge 2018**.
- Author listed in file: **Erik Thörnbald (Uppsala University)**.
- Uses MiniZinc global constraints via `include "globals.mzn"`.

## Model update summary

Added concise inline comments in model.mzn to clarify:

- team-assignment and score variable semantics,
- balance and request-satisfaction feasibility interpretation,
- objective intent as maximizing happiness while penalizing imbalance.
