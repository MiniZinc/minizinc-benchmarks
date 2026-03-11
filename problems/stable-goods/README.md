# Stable Goods

## Overview

This model describes a **stable allocation of indivisible goods with limited supply**. There are several people, several types of goods, and a fixed number of copies available for each good. Each person provides a ranked list of acceptable choices, where each choice says both:

- which good they want, and
- how many copies of that good they want.

The model assigns **exactly one acceptable choice** to each person. It must respect the available stock, and it looks for an assignment that is **stable** in the sense that no two people can reasonably complain by comparing each other’s allocations and swapping would-be improvements.

The optimization goal is to leave unused goods of **high value** whenever possible, which is equivalent to maximizing the total value of the remaining stock.

## Decision variables

For each person, the model chooses:

- `preference[p]`: which entry in that person’s preference list is selected,
- `good[p]`: the good assigned to that person,
- `num[p]`: how many copies of that good they receive.

For each good, it also computes:

- `remainder[g]`: how many copies are left unused after all assignments.

## Main constraints

### 1. Pick one acceptable request per person

Each person must receive one of the options from their own preference list. The selected `good` and `num` are derived from that chosen preference.

### 2. Do not exceed supply

For every good type, the total number allocated to all people plus the leftover amount must equal the available stock. This ensures the model never assigns more copies than exist.

### 3. Stability condition

The central constraint compares every pair of people. Informally, it prevents a pair from forming a **blocking situation** where one or both would prefer the other person’s assigned good and quantity, and the swap could be made feasible using the remaining stock.

The implementation uses:

- `rank[p,g]`: where good `g` appears in person `p`’s preference list, and
- `required[p,g]`: how many copies person `p` would need for good `g` if that option is listed.

The pairwise stability test is compact and somewhat subtle. A beginner-friendly reading is: for any two assigned people, at least one reason must exist why exchanging attention to the other person’s good does **not** create a justified objection.

## Objective

The model defines

- `objective = sum(g in GOOD)(remainder[g] * value[g])`

and **maximizes** it.

So the solver prefers solutions that leave behind goods with higher value. The model also prints

- `obj = sum(p in PERSON)(num[p] * value[good[p]])`

which is the total value of the goods actually assigned, but this is **not** the optimized quantity.

## Notes for beginners

- This is a **combinatorial optimization** model.
- Preferences are stored in a flattened format, then helper functions reconstruct each person’s list.
- The model includes an explicit search annotation using `int_search(...)`. Since benchmark descriptions should focus on the problem rather than solver guidance, that search strategy is not part of the conceptual problem statement.
- The exact economic interpretation of “stable” is inferred from the code. The model clearly captures pairwise stability with limited stock, but the original natural-language specification is not included here, so some interpretation details may be uncertain.

## Identifiable source / references

No paper or original citation is given inside the model file.

What can be identified from this repository:

- the benchmark is named **stable-goods**,
- it appears in the MiniZinc benchmark suite,
- `metadata.json` indicates use in the **MiniZinc Challenge 2020**.

If a more precise academic reference exists, it is not recorded in the local model or metadata available here.
