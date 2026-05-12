# Travelling Thief Problem (MiniZinc model overview)

## What problem is this model solving?
This model encodes the **Travelling Thief Problem (TTP)**, a combination of:
- a tour-planning problem (visit cities and return home), and
- a knapsack-packing problem (choose items to carry).

You start in city 1, must visit every city exactly once (and then return to city 1), and can pick items from cities. Items increase profit, but also increase carried weight, which slows travel speed and increases rental cost over time.

So the model balances two competing goals:
- pick valuable items, and
- avoid carrying so much weight that travel becomes too slow/expensive.

---

## Inputs (data)
The model expects:
- `CITY`, `ITEM`: sets of cities and items.
- `knapsack_capacity`: maximum total carried weight.
- `min_speed`, `max_speed`: speed range.
- `renting_ratio`: cost factor applied to travel time.
- `distances[CITY, CITY]`: pairwise city distances.
- `items[ITEM]`: each item has `profit`, `weight`, and assigned `city`.

It also computes `itemsPerCity` and checks that each non-start city has the same number of items.

---

## Decision variables
The main decisions are:
- `chosen[i]` (boolean): whether item `i` is taken.
- `order[t]` (city at position `t`): visiting order of cities.

Additional derived decision variables track the dynamic effect of packing:
- `weight[t]`: cumulative knapsack weight when leaving city at time `t`.
- `velocity[t]`: speed at time `t`, decreasing with `weight[t]`.
- `time[c]`: inverse mapping from city to its visit time.

---

## Core constraints
Key rules in the model:
- `order` is all-different: each city appears once in the tour sequence.
- `order[1] = City(1)`: tour starts at city 1.
- Total selected item weight must not exceed `knapsack_capacity`.
- `weight[1] = 0` and later weights accumulate picked items from visited cities.
- A dominance rule removes clearly inferior choices: if item `i` is heavier and no more profitable than item `j`, then selecting `i` under certain route-order conditions implies selecting `j`.

---

## Objective
The model maximizes:

`objective = 100 * profit - rental`

where:
- `profit` is total profit of selected items,
- `rental` is renting cost proportional to travel time, and
- travel time depends on city distances and speed (`distance / velocity`) at each leg.

Interpretation: prefer item sets and tours that give high value but keep weighted travel-time cost low.

---

## Notes and uncertainty
- This README explains the optimization model, not solver-specific search behavior.
- The model uses integer arithmetic (including division), so rental/time is discretized.
- `nu = (max_speed - min_speed) div knapsack_capacity` assumes positive capacity and may flatten speed changes for some parameter scales.
- The city-item mapping includes a placeholder for city 1; this appears consistent with the comment that city 1 has no items, but exact behavior depends on data consistency.
- The dominance constraint is sophisticated; its practical pruning effect depends on route timing and instance structure.

## Model update summary

Added concise inline comments in ttp.mzn to clarify:

- tour and item-selection decision variable semantics,
- knapsack and route feasibility constraints,
- objective intent as maximizing profit while penalizing rental time.

---

## Reference
- TTP context cited in the model comments: https://sites.google.com/view/ttp-gecco2023/home
