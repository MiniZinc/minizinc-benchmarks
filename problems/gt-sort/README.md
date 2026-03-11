# GT-Sort: Greedy Threshold Sort Optimisation

## Problem Description

This model studies the **Greedy Threshold Sort (GT-Sort)** problem, which is about finding the best (or worst) way to pair items in a binary tree computation that simulates a greedy subset-sum style algorithm.

Given `n` items, each with an associated weight coefficient `c[i]`, the model builds a **layered binary tree** (like a tournament bracket). At the bottom layer, each item is represented as the set `{0, c[i]}` — meaning it can either be excluded (0) or included (its weight). Moving up the tree, pairs of nodes at each layer are **merged**: the parent node holds all feasible pairwise sums of values from its two children, pruned by a capacity threshold `k`.

The key decision is: **in what order should items be paired up** at each layer of the tree? This pairing is represented by the variable `y`, and the model optimises over all valid pairings.

The model supports three modes via the `run` parameter:

| Mode       | Description                                            |
| ---------- | ------------------------------------------------------ |
| `BASELINE` | Items are paired in their natural left-to-right order. |
| `BEST`     | Find the pairing that **minimises** total set sizes.   |
| `WORST`    | Find the pairing that **maximises** total set sizes.   |

## Parameters

| Parameter | Description                                                                        |
| --------- | ---------------------------------------------------------------------------------- |
| `n`       | Number of items.                                                                   |
| `ub`      | Upper bound on item coefficients (weights).                                        |
| `c`       | Array of item coefficients (weights), one per item.                                |
| `f`       | Strictness factor (between 0 and 1). Controls how tight the capacity threshold is. |
| `run`     | Mode: `BASELINE`, `BEST`, or `WORST`.                                              |

## Derived Values

- `u` — Sum of all item weights (the maximum possible total).
- `k` — Capacity threshold, computed as `round(f * u)`. Any partial sum exceeding `k` is discarded from the sets.
- `L` — The set of layer indices, from 1 up to `ceil(log2(n)) + 1`. This is the depth of the binary tree.

## Variables

### `x[i, j]` — Node sets

The core variables. `x[i, j]` is the **set of feasible partial sums** at layer `i`, node `j`. Each value in the set is a possible total weight achievable by the items in that subtree, without exceeding the threshold `k`.

- Layer 1 is fixed: `x[1, j] = {0, c[j]}` for each item `j`.
- Higher layers are computed from the layer below via the pairing decisions.

### `y[i][j, 1..2]` — Pairing decisions

At each layer `i`, `y[i][j, 1]` and `y[i][j, 2]` give the indices of the **two child nodes** that are paired together to form parent node `j` in layer `i+1`. These are the decision variables that determine the structure of the tree.

## Objective

The objective is to **minimise** (for `BEST`) or **maximise** (for `WORST`) the total number of elements across all sets in the tree:

$$\text{obj} = \sum_{i,j} |x[i,j]|$$

A smaller total means more pruning occurred (values were cut off by the threshold `k` earlier), which is desirable for the `BEST` case. A larger total means less pruning, which is the `WORST` case.

## Constraints

- **Layer 1 initialisation**: The first layer is always fixed to the initial item sets.
- **Parent-child merging**: Each parent node at layer `i+1` contains exactly the set of sums `a + b` for all `a` in one child and `b` in the other child, where `a + b ≤ k`.
- **Valid pairing**: All child indices used in pairings at a given layer are distinct (`alldifferent`).
- **Symmetry breaking**: Child pairs are ordered so that left indices are strictly increasing across pairs, and within each pair the left index is smaller than the right.
- **Baseline fixing**: In `BASELINE` mode, the pairing is fixed to the natural order.

## Notes and Uncertainty

- The exact origin of this problem is not entirely clear from the model. It appears to be related to combinatorial optimisation of sorting/merging networks or greedy algorithms for the 0/1 knapsack or subset-sum problem. The "GT" in "GT-Sort" likely refers to **Greedy Threshold**.
- The comment `% TODO don't count the 0's in the sets` suggests the objective may be slightly over-counting, as the padded zero values in sets contribute to the sum. This may affect the exact interpretation of the objective value.
- The model was modified by MiniZinc Challenge organisers (refactoring `y` variables and moving `c` to data files), and appeared in the **2025 MiniZinc Challenge**.

## References

- If this model is based on an academic paper, the reference could not be confirmed at the time of writing. The structure resembles work on **parallel prefix sum networks** or **greedy knapsack algorithms**. An expert familiar with the 2025 MiniZinc Challenge may be able to provide a more precise reference.
