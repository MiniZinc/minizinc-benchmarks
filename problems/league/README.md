# League — Group Tournament Formation

This MiniZinc model solves the problem of dividing participants into **balanced groups** for a round-robin or group-stage tournament. Two competing goals must be balanced: keeping players of similar skill together, while ensuring each group has players from a variety of countries.

This problem appeared in the **MiniZinc Challenge 2012 and 2013**.

---

## Problem Description

Given a set of players, each with a **ranking** (skill level) and a **country of origin**, the task is to partition them into groups of roughly equal size. A good assignment achieves two things at once:

1. **Ranking balance** — the spread between the best and worst ranked player in each group should be as small as possible.
2. **Country diversity** — each group should contain players from as many different countries as possible.

These two goals are combined into a single objective function that strongly prioritises ranking balance, with country diversity as a secondary consideration.

---

## Parameters

| Parameter            | Description                                                               |
| -------------------- | ------------------------------------------------------------------------- |
| `n`                  | Total number of players                                                   |
| `n_persons_in_group` | Maximum number of players allowed in one group                            |
| `ranking[i]`         | Skill ranking of player `i` (integer; higher values indicate lower skill) |
| `country[i]`         | Country identifier for player `i` (integer code)                          |

From these, the number of groups is derived automatically:

$$\text{n\_groups} = \left\lceil \frac{n}{\text{n\_persons\_in\_group}} \right\rceil$$

Each group will contain either `n_persons_in_group` or `n_persons_in_group − 1` players (groups are filled as evenly as possible).

---

## Decision Variables

| Variable                       | Description                                                       |
| ------------------------------ | ----------------------------------------------------------------- |
| `assign_to[i]`                 | The group number (1 to `n_groups`) that player `i` is assigned to |
| `n_persons[g]`                 | The number of players in group `g`                                |
| `max_rank[g]`                  | The highest (worst) ranking among players in group `g`            |
| `min_rank[g]`                  | The lowest (best) ranking among players in group `g`              |
| `rank_diff[g]`                 | The ranking spread in group `g`: `max_rank[g] − min_rank[g]`      |
| `countries_in_group_tmp[g, c]` | 1 if country `c` is represented in group `g`, 0 otherwise         |
| `countries_in_group[g]`        | The number of distinct countries represented in group `g`         |

The central decision is the `assign_to` array — once players are assigned to groups, all other variables are determined.

---

## Constraints

1. **Group size** — Every group contains either `n_persons_in_group` or `n_persons_in_group − 1` players, ensuring a balanced partition.
2. **Ranking spread** — `rank_diff[g]` is computed as the difference between the maximum and minimum ranking within each group.
3. **Country counting** — `countries_in_group[g]` counts how many distinct countries appear in group `g` using the auxiliary binary array `countries_in_group_tmp`.
4. **Symmetry breaking** — Groups are ordered by their minimum and maximum rankings to avoid counting equivalent solutions multiple times.

---

## Objective

The model **minimises** the following combined objective:

$$\text{objective} = 100 \times \sum_{g} \text{rank\_diff}[g] \;-\; \sum_{g} \text{countries\_in\_group}[g]$$

- The **first term** (weighted by 100) drives the solver to find groups where players have similar skill levels. The large weight makes this the dominant priority.
- The **second term** (subtracted, so maximised) rewards diversity by favouring assignments where each group contains players from many different countries.

The factor of 100 means that reducing the total ranking spread by 1 is considered far more valuable than adding one extra country to a group.

---

## Instance Naming

The provided data instances follow the naming convention `model{n}-{a}-{b}`, where `n` is the total number of players. The meaning of `{a}` and `{b}` in the filename is not entirely clear from the model alone — they may encode the number of ranking tiers or countries present in that instance. Expert clarification on the instance naming convention would be welcome.

---

## References

This problem was used in the **MiniZinc Challenge 2012** and **MiniZinc Challenge 2013**. No specific academic paper has been identified as the original source of this problem formulation. If you are aware of a related publication, please add a reference here.
