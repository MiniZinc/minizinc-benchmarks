# Steiner Systems

## Problem Description

A **Steiner system** `S(t, k, N)` is a classic combinatorial design problem from mathematics. Given:

- a universe `X` of `N` elements (integers `1` to `N`),
- a target **tuple size** `t`,
- a **block size** `k`,

the goal is to find a collection of subsets of `X` — called **blocks** — each of size exactly `k`, such that **every group of `t` elements from `X` appears together in exactly one block**.

A well-known special case is the **Steiner triple system** `S(2, 3, N)`: partition pairs of points into triples so that every pair of points shares exactly one triple. The smallest non-trivial example is the **Fano plane** `S(2, 3, 7)`, which has 7 triples covering all 21 pairs of 7 points.

## Parameters

| Parameter | Meaning                                                 |
| --------- | ------------------------------------------------------- |
| `N`       | Total number of elements in the universe                |
| `t`       | Size of the sub-group that must be covered exactly once |
| `k`       | Size of each block                                      |

The number of required blocks is determined by combinatorics and is not a free variable:

$$m = \binom{N}{t} \Big/ \binom{k}{t}$$

## Decision Variables

```
array [1..m] of var set of 1..N: C
```

`C` is an array of `m` sets. Each `C[i]` is a subset of the universe `X` that the solver must assign. Together, these sets form the complete Steiner system.

## Constraints

1. **Block size** — Every block contains exactly `k` elements:

   ```
   forall i: card(C[i]) = k
   ```

2. **Coverage uniqueness** — Any two distinct blocks overlap in at most `t − 1` elements. Because the total block count `m` is pre-computed to cover every `t`-subset exactly once, this upper-bound on pairwise intersection is sufficient to enforce the "exactly one" coverage property:

   ```
   forall i < j: card(C[i] ∩ C[j]) ≤ t − 1
   ```

3. **Symmetry breaking** — Blocks are required to appear in lexicographic order to eliminate equivalent permutations of the same solution:
   ```
   forall i: C[i] < C[i+1]
   ```

## Objective

This is a **pure satisfaction problem** — there is no objective function to minimise or maximise. The solver simply needs to find one valid assignment of blocks that satisfies all constraints, or prove that none exists.

## Instances

The benchmark includes five instances used in the MiniZinc Challenge 2021:

| Instance file            | `t` | `k` | `N` | Blocks `m` |
| ------------------------ | --- | --- | --- | ---------- |
| `steiner_t2_k7_N21.json` | 2   | 7   | 21  | 21         |
| `steiner_t3_k3_N11.json` | 3   | 3   | 11  | 165        |
| `steiner_t3_k4_N8.json`  | 3   | 4   | 8   | 14         |
| `steiner_t4_k4_N10.json` | 4   | 4   | 10  | 45         |
| `steiner_t6_k6_N7.json`  | 6   | 6   | 7   | 1          |

> **Note on existence:** Not every combination of `(t, k, N)` admits a valid Steiner system. Whether a solution exists for a given set of parameters is a deep open question in combinatorics for many cases. Some instances in this benchmark may therefore be unsatisfiable.

## References

- Hanani, H. (1960). _On quadruple systems_. Canadian Journal of Mathematics, 12, 145–157.
- Stinson, D. R. (2004). _Combinatorial Designs: Constructions and Analysis_. Springer.
- Wikipedia: [Steiner system](https://en.wikipedia.org/wiki/Steiner_system)
