# Group Splitter

## Problem Description

The **Group Splitter** problem models a group activity recommendation scenario. A group of people wants to attend two sequential activities — for example, going to a cinema followed by a restaurant. Rather than requiring everyone to attend the same venue, the group can be **split into subgroups** for each activity phase, so that each subgroup attends a venue that better matches the preferences of its members.

The problem has two phases:

- **Phase 1** – the first activity (e.g., cinema, event)
- **Phase 2** – the second activity (e.g., restaurant, bar)

A user may be in a different subgroup for phase 1 than for phase 2, allowing maximum flexibility in matching people to activities they prefer.

The goal is to find an assignment of users to subgroups and activities, together with a valid schedule, that **maximises a combined satisfaction score** based on individual user preferences and publicly available venue ratings.

This problem has appeared in the MiniZinc Challenge in 2017, 2019, and 2025. It was developed by Jacopo Mauro and Tong Liu at the University of Bologna.

---

## Data

Each instance describes:

- A set of **users**, each with personal preference ratings for every candidate activity in both phases.
- A set of **phase-1 activities** (e.g., cinemas), each with a time window (earliest start, latest end), a duration, a geographic location (grid cell), and a public rating.
- A set of **phase-2 activities** (e.g., restaurants), described in the same way.
- A **distance matrix** between geographic cells, representing travel time between locations.
- Global parameters controlling the minimum subgroup size (`min_group_size`), the maximum allowed waiting time between the two activities (`max_wait`), the earliest permitted start time (`startAfter`), and the preference-vs-public-rating balance parameter (`eta`).

The real-world instances contain thousands of candidate venues sourced from an actual city, making the search space very large.

---

## Decision Variables

| Variable                                              | Meaning                                                                   |
| ----------------------------------------------------- | ------------------------------------------------------------------------- |
| `user_group_map1[u]`                                  | Which subgroup user `u` belongs to for phase 1                            |
| `user_group_map2[u]`                                  | Which subgroup user `u` belongs to for phase 2                            |
| `group_act_map1[g]`                                   | Which phase-1 activity subgroup `g` attends                               |
| `group_act_map2[g]`                                   | Which phase-2 activity subgroup `g` attends                               |
| `user_act_map1[u]`                                    | Phase-1 activity attended by user `u` (derived from the group assignment) |
| `user_act_map2[u]`                                    | Phase-2 activity attended by user `u`                                     |
| `user_start_time_map1[u]`                             | Start time of user `u`'s phase-1 activity                                 |
| `user_start_time_map2[u]`                             | Start time of user `u`'s phase-2 activity                                 |
| `user_duration_map1[u]`                               | Duration of user `u`'s phase-1 activity                                   |
| `user_duration_map2[u]`                               | Duration of user `u`'s phase-2 activity                                   |
| `user_end_map1[u]` / `user_end_map2[u]`               | End of the time window for each activity                                  |
| `user_cell_map1[u]` / `user_cell_map2[u]`             | Geographic cell of the activity venue                                     |
| `user_pub_rating_map1[u]` / `user_pub_rating_map2[u]` | Public rating (0–5) of the chosen venue                                   |
| `user_weight_map1[u]` / `user_weight_map2[u]`         | User's personal preference rating (−2 to +2) for the chosen activity      |
| `user_distance_map[u]`                                | Travel time for user `u` between their phase-1 and phase-2 venues         |

---

## Constraints

1. **Minimum subgroup size** – Every subgroup must contain at least `min_group_size` members (enforced for both phases independently).
2. **Activity consistency** – A user's activity is always the activity assigned to their subgroup.
3. **Time window feasibility** – Each user must start their activity within the venue's opening time window, and must finish before it closes.
4. **Travel and sequencing** – The start of phase 2 must be at least as late as the end of phase 1 plus the travel time between the two venues.
5. **Maximum wait** – The gap between finishing phase 1 and starting phase 2 must not exceed `max_wait`.
6. **Earliest start** – All phase-1 activities must start no earlier than `startAfter`.

Table constraints are used throughout to link activity properties (time windows, duration, location, public rating) and user preference weights to the chosen activity indices.

---

## Objective

The model **maximises** a weighted sum of four terms:

$$\text{objective} = \eta \cdot \sum_u w_1[u] + (10-\eta) \cdot \sum_u r_1[u] + (10-\eta) \cdot \sum_u r_2[u] + \eta \cdot \sum_u w_2[u]$$

where:

- $w_1[u]$, $w_2[u]$ are the **personal preference scores** of user $u$ for their chosen phase-1 and phase-2 activities (range −2 to +2).
- $r_1[u]$, $r_2[u]$ are the **public ratings** of those venues (range 0 to 5).
- $\eta$ (range 0–10) is a parameter that **balances personal preferences against public quality**. Higher $\eta$ weights individual tastes more; lower $\eta$ weights public venue quality more.

---

## Notes

- The model uses symmetry-breaking constraints to reduce equivalent assignments: user 1 is always placed in group 1 for both phases, and subsequent users are constrained to join an existing group or the next new group.
- The problem is marked as a combinatorial optimisation problem (`combi`) with a maximisation objective.
- A specific academic paper describing this model could not be confirmed. The authors listed in the model header are Jacopo Mauro (University of Bologna / INRIA) and Tong Liu (University of Bologna). An expert familiar with their publications may be able to provide a precise citation.

## Model update summary

Added concise inline comments in group.mzn to clarify:

- phase-wise group and activity assignment variable semantics,
- objective interpretation as weighted personal/public satisfaction,
- maximization intent for two-stage recommendation quality.
