# Grid Colouring

## Problem Description

The Grid Colouring problem asks: what is the minimum number of colours needed to colour every cell of an `n × m` grid such that **no axis-aligned rectangle has all four of its corners the same colour**?

More precisely, consider any four cells that form the corners of an axis-aligned rectangle — that is, cells at positions (row `i`, column `k`), (row `i`, column `l`), (row `j`, column `k`), and (row `j`, column `l`) for any two distinct rows `i < j` and two distinct columns `k < l`. The constraint requires that these four corners are **not** all assigned the same colour. At least one pair of adjacent corners must differ.

The goal is to find a valid colouring that uses as few colours as possible.

## Parameters

| Parameter | Description                               |
| --------- | ----------------------------------------- |
| `n`       | The width of the grid (number of columns) |
| `m`       | The height of the grid (number of rows)   |

## Variables

| Variable    | Description                                                                                                                       |
| ----------- | --------------------------------------------------------------------------------------------------------------------------------- |
| `x[i, k]`   | The colour assigned to the cell at row `i`, column `k`. Each colour is represented by an integer in the range `1` to `min(n, m)`. |
| `objective` | The total number of distinct colours used in the colouring. This is the value being minimised.                                    |

## Constraints

1. **Colour bound**: Every cell's colour must be at most `objective`, ensuring `objective` correctly tracks the number of colours in use.

2. **No monochromatic rectangle**: For every set of four cells forming the corners of an axis-aligned rectangle, it is forbidden for all four corners to share the same colour. Equivalently, at least one pair of adjacent corners of every such rectangle must have different colours.

## Objective

**Minimise** `objective` — the number of colours used.

## Example

For a 3 × 3 grid, a valid minimum colouring would assign colours to cells such that you can never pick two rows and two columns where the four intersection cells are identically coloured.

## Background and Related Work

This problem belongs to a family of combinatorial colouring problems related to **anti-Ramsey theory** and **discrepancy theory**. The "no monochromatic rectangle" condition on grids has been studied in combinatorics, where the question of how many colours are sufficient to avoid such patterns is of theoretical interest.

The problem is also a natural benchmark for constraint programming solvers, as it combines a tight combinatorial structure with a minimisation objective, making it challenging for both exact and heuristic methods.

> **Note**: The precise academic origin of this specific MiniZinc formulation is uncertain. If you are aware of a specific paper or competition this model derives from, please update this README with the appropriate reference.

## Model update summary

Added concise inline comments in GridColoring.mzn to clarify:

- grid colour decision variable semantics,
- objective interpretation as minimal colour bound,
- optimization intent for rectangle-avoidance colouring.
