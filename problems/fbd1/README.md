# FBD1 Design Construction Model

## Overview

This MiniZinc model constructs an **FBD1 design**, which is a type of combinatorial design used in experimental design and related optimisation problems. The goal is to determine a set of design parameters that satisfy specific uniqueness and ordering constraints while minimising the overall design size.

---

## Problem Description

The model aims to generate a design with `k` main factors. Each factor is associated with a numeric value, and these values must satisfy certain mathematical relationships to ensure the design is valid. The design size is calculated based on these values, and the objective is to minimise this size.

---

## Key Parameters

- `k`: Number of main factors in the design (read from a `.dzn` data file).
- `maxn`: Upper bound for design size, computed as `5 + k^3`.

---

## Decision Variables

- `n[i]`: Array of size `k`, representing the design values for each main factor. Each `n[i]` is in the range `1..maxn div 2`.
- `n_star`: An additional design variable used in calculating the design size.
- `N`: The total design size, computed as:
  \[
  N = 2 \times n[k] + n\_\text{star}
  \]

---

## Derived Variables

- `Q`: Array where each element is `2 * n[i]`.
- `T_plus`: Pairwise sums of design values (`n[j] + n[i]` for `i < j`).
- `T_minus`: Pairwise differences of design values (`n[j] - n[i]` for `i < j`).
- `Q_folded` and `T_plus_folded`: Adjusted values incorporating `n_star` and `n[k]`.

---

## Constraints

1. **Ordering**: Design values must be strictly increasing:
   \[
   n[i] < n[i+1] \quad \text{for all } i < k
   \]
2. **Uniqueness**: All computed indicator frequencies (from `n`, `Q`, `T_plus`, `T_minus`, etc.) must be distinct:
   \[
   \text{alldifferent}(n \cup T*\text{minus} \cup T*\text{plus} \cup Q \cup T*\text{plus_folded} \cup Q*\text{folded})
   \]
3. **Bounds**:
   - `n_star <= 2 * n[k] + 1`
   - `n[i] >= i` for all factors.
   - `Q[i] >= 2 * i` for all factors.
4. **Sequential Constraints**:
   - `n[j] != Q[i]` for `i < j`.
   - `n[j] != 3 * n[i]` for `i < j`.

---

## Objective

Minimise:
\[
\text{objective} = N = 2 \times n[k] + n\_\text{star}
\]
This ensures the smallest possible design size while satisfying all constraints.

---

## Notes

- Small instances (`k = 2` or `k = 3`) are easy to solve.
- Larger instances (`k >= 10`) become computationally challenging.
- The model uses global constraints like `alldifferent` for uniqueness.

---

### References

- Related to combinatorial design theory and experimental design optimisation.
- For more details, see literature on **Factorial Balanced Designs (FBD)**.
