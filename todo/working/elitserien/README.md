# Elitserien Handball Scheduling

## Problem Description

This model schedules the season fixtures for **Elitserien**, the top division of Swedish handball. The league consists of 14 teams split into two geographic divisions — North (7 teams) and South (7 teams) — and the task is to produce a complete schedule of matches that satisfies a rich set of sporting and logistical constraints.

The model was developed by Jeff Larson (KTH) and Mats Carlsson (SICS) and has appeared in the MiniZinc Challenge since 2014. The problem is an instance of the broader class of _sports league scheduling_ problems studied in the operations research literature (see, e.g., Rasmussen & Trick, _Sport scheduling_, in _Handbook of Combinatorial Optimization_, Springer, 2008).

## Season Structure

The 14-team season is divided into **20 rounds**, structured as follows:

1. **Rounds 1–7 (Divisional phase):** Each division holds its own Single Round-Robin Tournament (SRRT), so every team within a division plays each other team in the division exactly once. Each team has exactly one **bye** (a rest week with no match) during this phase.
2. **Rounds 8–20 (League phase):** Two full SRRTs are played across the complete 14-team league. The second of these 13-round tournaments is the mirror image of the first (home and away venues swapped).

## Decision Variables

| Variable           | Meaning                                                                                                                                        |
| ------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| `hap[t, p]`        | The _Home-Away Pattern_ for team `t` in round `p`: `H` (home), `A` (away), or `B` (bye).                                                       |
| `contestant[t, p]` | The opponent faced by team `t` in round `p`. If team `t` has a bye, this is set to `t` itself.                                                 |
| `break[t]`         | The round in which team `t` has a _break_ — two consecutive home games or two consecutive away games. Teams with no break have `break[t] = 0`. |
| `row[t]`           | Maps each real-world team `t` to a row in the schedule template (used to handle divisional structure internally).                              |
| `team[r]`          | The inverse of `row`: maps each template row `r` back to the corresponding team.                                                               |

## Constraints

The schedule must satisfy the following requirements:

- **Round-robin structure:** In every round, opponents are paired consistently — if team A plays team B, then team B plays team A (enforced via `inverse`). Within the divisional phase, teams only face opponents from their own division.
- **Each team plays each opponent exactly once** in the divisional phase and exactly once (then again in the mirror) in the league phase (`alldifferent`).
- **HAP regularity:** The sequence of home, away, and bye slots for each team must follow a specific pattern encoded as a finite automaton (`regular`). This enforces constraints such as: no overly long runs of home or away games, and byes only in the divisional phase.
- **Break distribution:** Every team that has a break must have it occur during a specific set of round numbers (9, 11, 13, 15, 17, or 19). Each division has exactly 6 teams with a break, and exactly 2 teams share each permissible break round (`global_cardinality_closed`).
- **Home/away balance:** At no point during the season can the number of home games and away games played by any team differ by more than 1 (this is implied by the HAP regularity constraint).
- **Alternating Venue Rule (AVR):** Any two teams that meet multiple times must play at different venues in consecutive encounters.
- **Complementary schedules:** Within each division, at least 3 pairs of teams must have _complementary_ HAP patterns — in every round, one partner plays at home while the other plays away (or both have byes simultaneously).
- **Derby constraints:** Certain regional rivalry matches (derbies) must be played in specified rounds, provided as input data.
- **Venue unavailability:** Each team may have rounds in which their home venue is unavailable. These are encoded in the `nohome` input array.

## Objective

The model **minimises** the number of scheduling conflicts caused by venue unavailability. Specifically, it counts the number of times a team is assigned a home game in a round when their venue is unavailable, across all 33 effective rounds of the season (including the mirrored second leg). A perfect schedule achieves an objective value of 0.

## Input Data

Each problem instance provides:

- `nohome[t, p]` — a 0/1 matrix indicating which teams cannot host home games in which rounds.
- `group1`, `group2` — the assignment of teams to the North and South divisions.
- `derby_set`, `derby_period` — sets of rival teams and the round in which their derby must be scheduled.
- `cpairs` — pairs of teams that must have complementary schedules.

## Notes

- The model uses a template-based approach via the `row`/`team` variables. The 14 rows of the template are pre-structured so that structural symmetries (e.g., satisfying the HAP regularity and break-distribution constraints) are partially handled by construction. Real teams are then assigned to template rows, and the divisional assignment constrains which rows a team may occupy.
- Some constraints visible in the model are commented out (e.g., additional symmetry-breaking rules). These may be candidates for strengthening the model and are noted here for the benefit of future maintainers.
