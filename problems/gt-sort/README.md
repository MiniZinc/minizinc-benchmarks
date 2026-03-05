# GT-Sort Model

## Overview

This MiniZinc model implements a **generalised tree-based sorting and subset sum generation problem**. The goal is to construct a layered tree structure where each node contains a set of possible sums derived from its child nodes. The model is parameterised by a set of coefficients and a strictness factor, and aims to minimise (or maximise) the total size of all sets in the tree.

---

## Problem Description

- We start with an array of coefficients `c` representing weights or values.
- These coefficients are placed in the first layer of a tree as singleton sets.
- Each subsequent layer combines pairs of sets from the previous layer to form new sets containing all possible sums of elements from the paired sets, subject to an upper bound `k`.
- The tree is constructed layer by layer until only one node remains at the top.
- The objective is to minimise the total number of elements across all sets in the tree (or maximise in the worst-case scenario).

This approach is useful for problems involving subset sums, combinatorial optimisation, and tree-based dynamic programming.

---

## Key Parameters

- `n`: Number of coefficients (size of the problem).
- `ub`: Upper bound for generating coefficients.
- `f`: Strictness factor used to compute `k`.
- `c`: Array of coefficients (input values).
- `k`: Maximum allowed sum for any node, computed as `round(f * u)` where `u` is the sum of the largest elements in each initial set.
- `L`: Set of layers in the tree, calculated as `1..(1 + ceil(log2(length(c))))`.

---

## Decision Variables

- `x[i,j]`: A set of integers representing possible sums at layer `i` and node `j`.
  - Layer 1 (`x[1,..]`) is fixed to the initial sets derived from `c`.
  - Higher layers are computed by combining child sets from the previous layer.
- `y`: Pairing variables that determine which nodes in a layer are combined to form parent nodes in the next layer.
- `obj`: Sum of the cardinalities of all sets in the tree.
- `objective`: The optimisation target:
  - Minimise `obj` for normal or baseline runs.
  - Maximise `obj` for worst-case runs.

---

## Constraints

1. **Initial Layer**:
   - The first layer is fixed to sets `{0, ci}` for each coefficient `ci`.
2. **Tree Construction**:
   - Each parent node contains all possible sums of elements from its two child nodes, provided the sum does not exceed `k`.
3. **Pairing Rules**:
   - Pairing variables ensure that nodes are combined correctly and symmetrically.
   - Unused nodes in layers are assigned empty sets.
4. **Symmetry Breaking**:
   - Enforces ordering constraints on pairing to reduce redundant solutions.

---

## Objective

Minimise:
\[
\text{objective} = \sum\_{\text{all nodes}} \text{cardinality of sets}
\]
or maximise in the worst-case scenario.

---

## Notes

- This model demonstrates advanced use of **set variables** and **layered constraints** in MiniZinc.
- It can be adapted for subset sum problems, knapsack approximations, and combinatorial tree optimisations.
- The parameter `run` allows switching between baseline, best, and worst-case scenarios.

---
