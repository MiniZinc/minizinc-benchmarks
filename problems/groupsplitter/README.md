# Group Splitter

This directory contains a MiniZinc model (`group.mzn`) for the **group splitting** problem.  
A set of users want to be divided into sub‑groups and assigned to activities in two phases such that
preferences are respected and scheduling constraints are met.  The model produces a recommendation of
which users should go into which subgroup, what activity each subgroup should do, and when.

## Key Concepts and Inputs

- **Users**: identified by `user_ids`.
- **Activities**: two phases (`activity1_ids` and `activity2_ids`), each with a catalog of options.
- **Groups / Cells**: sub‑groups of users (`group_ids`, `cell_ids`).
- **Preferences**: each user rates phase‑1 and phase‑2 activities (`preferences1`, `preferences2`).
- **Distances**: a symmetric matrix `distances` between cells (used to model travel times).
- **Ratings**: public and individual rating domains used for balance (`pub_rating_domain`, `user_rating_domain`).

Additional parameters control the problem:
- `min_group_size` – minimum number of users per subgroup.
- `max_wait` – maximum allowed waiting time between activities.
- `startAfter` – earliest starting time for any activity.
- `eta` – weight balancing public vs. user ratings.

## Decision Variables

The solver chooses:

- A subgroup membership for each user in both phases (`user_group_map1`, `user_group_map2`).
- Which activity each group performs (`group_act_map1`, `group_act_map2`).
- Each user’s assigned activity, start time, duration, cell and ratings maps for both phases.

## Objective and Constraints

The model enforces:

1. Every group has at least `min_group_size` members.
2. Users’ personal activity assignments agree with their group’s activity.
3. Temporal constraints ensure activities respect availability, durations, and travel times.
4. Symmetry-breaking constraints reduce redundant solutions.

The objective (not shown explicitly) maximises compatibility of assignments according to the
`eta` parameter, weighting public and private ratings, while respecting the constraints above.

The model uses `table` and `count` global constraints for efficiency.
