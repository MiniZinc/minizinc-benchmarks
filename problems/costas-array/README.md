# Costas Array

## Problem Description

A **Costas array** of order $n$ is a permutation of the integers $\{1, 2, \ldots, n\}$ with a special property related to the distances between elements.

Imagine placing $n$ tokens on an $n \times n$ grid, one per row and one per column (like non-attacking rooks in chess). A Costas array guarantees that every pair of tokens defines a unique displacement vector — no two pairs of tokens are the same distance apart in both the horizontal and vertical directions simultaneously. This makes Costas arrays useful in radar and sonar signal design, where you want pulse patterns that are easy to distinguish from shifted versions of themselves.

The defining property is checked using a **triangular difference table**. Given the permutation, you compute the differences between elements that are $i$ positions apart, for each gap size $i$ from 1 to $n-1$. Each of these $n-1$ rows of differences must itself contain only distinct values. For example, the permutation $\{1, 3, 4, 2, 5\}$ has difference rows $\{2, 1, -2, 3\}$, $\{3, -1, 1\}$, $\{1, 2\}$, and $\{4\}$ — all distinct within each row, so it is a valid Costas array.

This is a **satisfaction problem**: there is no objective to optimise; the goal is simply to find all valid Costas arrays of a given size, or to confirm one exists.

## Input Parameters

| Parameter | Description                                                                       |
| --------- | --------------------------------------------------------------------------------- |
| `n`       | The order (size) of the Costas array — the permutation is over $\{1, \ldots, n\}$ |

## Decision Variables

| Variable      | Type                                     | Description                                                                                           |
| ------------- | ---------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| `costas`      | `array[1..n] of var 1..n`                | The Costas array itself — a permutation of $\{1, \ldots, n\}$                                         |
| `differences` | `array[1..n, 1..n] of var -(n-1)..(n-1)` | The difference table; `differences[i,j]` holds `costas[j] - costas[j-i]` for $i < j$, and 0 otherwise |

## Constraints

1. **Permutation**: `costas` is an all-different array (each value from 1 to $n$ appears exactly once).
2. **Difference definition**: For each pair $(i, j)$ with $i < j$, `differences[i,j]` is set to `costas[j] - costas[j-i]`. This captures how far apart elements are when skipping $i$ positions.
3. **Row uniqueness**: For each gap size $i$, all the differences in row $i$ of the difference table must be distinct (enforced with `alldifferent`).

The model also includes two **redundant constraints** (present only to help the solver work faster, not logically required):

- No difference can be zero (since the array is a permutation, this is implied, but stating it explicitly can help pruning).
- A consistency condition between neighbouring cells of the difference table.

A **symmetry-breaking constraint** is also applied: `costas[1] < costas[n]`, which eliminates one of each pair of mirror-image solutions.

## Objective

This is a **pure satisfaction** problem — there is no objective function. The model simply searches for permutations of $\{1, \ldots, n\}$ that satisfy the Costas property.

## Background and References

Costas arrays were introduced by John P. Costas in the context of sonar and radar signal design. They have been studied extensively in combinatorics and have connections to permutation theory and frequency-hopping spread-spectrum communications.

- Costas, J. P. (1984). "A study of a class of detection waveforms having nearly ideal range-Doppler ambiguity properties." _Proceedings of the IEEE_, 72(8), 996–1009.
- Drakakis, K. (2006). "A review of Costas arrays." _Journal of Applied Mathematics_, 2006. [doi:10.1155/JAM/2006/26385](https://doi.org/10.1155/JAM/2006/26385)
- MathWorld entry: [https://mathworld.wolfram.com/CostasArray.html](https://mathworld.wolfram.com/CostasArray.html)

The model was contributed by Barry O'Sullivan (Cork Constraint Computation Centre, Ireland, September 2009).

## Model update summary

Added concise inline comments in `CostasArray.mzn` to clarify:

- the core variables (`costas` permutation and `differences` triangular table),
- the row-uniqueness constraint that defines the Costas array property,
- the symmetry-breaking and redundant constraints used to assist solving.
