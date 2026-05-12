# Traveling Tournament Problem with Predefined Venues (TTPPV)

This MiniZinc model schedules a **single round-robin tournament**: every team plays every other team exactly once.  
The twist is that the venue of each matchup is already fixed in advance (home vs away), and the goal is to build a feasible schedule that **minimizes total travel distance**.

## What problem is being solved?

Given `nbTeams` teams and `nbRounds = nbTeams - 1` rounds, the model must decide who each team plays in each round, while respecting:

- every pair meets exactly once,
- no team plays itself,
- home/away pattern for each pair is fixed by input `pv`,
- no team has more than 3 consecutive home games,
- no team has more than 3 consecutive away games.

Distance is specialized to **circular instances** (teams arranged on a circle), where distance between teams is the shorter circular arc.

## Main variables (beginner view)

- `opponent[i,k]` (decision variable): opponent of team `i` in round `k`.
- `venue[i,k]` (derived variable): whether team `i` is at home (`1`) or away (`2`) in round `k`.
- `travel[i,k]` (derived variable): travel distance for team `i` for trip segment `k`.
  - Includes travel to first game, between rounds, and return home after last round.
- `objective`: total travel over all teams and travel segments.

## How constraints shape the schedule

1. **Round-robin consistency**
   - `opponent[i,k] != i` (no self-match).
   - If `i` plays `j`, then `j` plays `i` in same round.
   - Each team sees all other teams exactly once (`alldifferent` across rounds).

2. **Per-round matching structure**
   - Opponent values in a round are all different (helps enforce valid pairing structure).

3. **Predefined venues**
   - `venue[i,k] = pv[i, opponent[i,k]]`, so home/away comes directly from input pair data.

4. **Home/away streak limit**
   - A `regular` automaton enforces at most 3 consecutive home games and at most 3 consecutive away games for each team.

5. **Travel computation**
   - Travel is computed from venue transitions:
     - home→home: `0`,
     - away→home: current away venue back home,
     - home→away: home to next away venue,
     - away→away: between away venues.
   - Also handles first departure and final return.

## Objective

The model **minimizes**:

\[
\text{objective} = \sum_{i \in Teams} \sum_{k \in Travels} travel[i,k]
\]

So the solver seeks the feasible tournament schedule with minimum total team travel.

## Output

The model prints:

- a compact schedule view (with `@` marking away games),
- arrays for `opponent`, `venue`, and `travel`,
- final `objective` value.

## Uncertainty / assumptions

- The model comment indicates `pv[i][j] = 1` means “team `i` plays at home vs `j`”; value `2` is therefore interpreted as away.
- Distances are generated internally using a circular formula; this is appropriate for CIRC benchmark instances, but not for arbitrary geographic distance matrices.
- The per-round `alldifferent` on opponents is likely redundant in strict graph-theoretic terms but can still strengthen propagation.

## References (identifiable from repository context)

- Problem family: **Traveling Tournament Problem with Predefined Venues (TTPPV)**.
- Challenge usage in this repository metadata: MiniZinc Challenge years **2014**, **2017**, **2022** for CIRC-labeled instances.
- Related classical context: Traveling Tournament Problem (sports timetabling literature), with TTPPV as a venue-fixed variant.

## Model update summary

Added concise inline comments in ttppv.mzn to clarify:

- opponent, venue, and travel decision variable semantics,
- round-robin and streak-limit feasibility constraints,
- objective intent as minimizing total team travel.
