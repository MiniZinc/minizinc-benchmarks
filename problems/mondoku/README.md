# Mondoku Puzzle Model

## Overview

This MiniZinc model generates solutions for an **Irregular Mondoku Puzzle**, a grid-based artistic puzzle inspired by Sudoku-like constraints but focused on colour grouping. The puzzle consists of a rectangular grid where each cell is assigned a colour. The key rule is that **each row and column must contain exactly one contiguous group of each colour**.

The model also aims to produce a visually balanced solution by minimising the difference in colour distribution across rows and columns.

---

## Problem Description

- The grid has dimensions `W × H` (width and height).
- There are `C` distinct colours.
- Each row and column must include all colours, but each colour appears in **one contiguous block** (group) per row and per column.
- For example:
  - Allowed: `RRGG` (two reds followed by two greens).
  - Not allowed: `RGGR` (greens split into two separate groups).

The optimisation goal is to make the distribution of colours as balanced as possible across the grid.

---

## Key Components

### Parameters

- `W`: Width of the grid.
- `H`: Height of the grid.
- `C`: Number of colours.
- `Colors`: Set of colour identifiers `{1..C}`.
- `Width`: Set of column indices `{1..W}`.
- `Height`: Set of row indices `{1..H}`.

### Decision Variables

- `puzzle[w,h]`: The colour assigned to cell `(w,h)`.

### Derived Variables

- `across[w,h]`: Indicates the start of a colour group in a row (otherwise 0).
- `down[w,h]`: Indicates the start of a colour group in a column (otherwise 0).

### Constraints

1. **Row Group Constraint**:
   - Each row must contain exactly one group for each colour.
   - Implemented using `global_cardinality` on `across`.
2. **Column Group Constraint**:
   - Each column must contain exactly one group for each colour.
   - Implemented using `global_cardinality` on `down`.

### Optimisation

- For each row and column, compute:
  - `diff_across[h]`: Difference between the maximum and minimum occurrences of colours in row `h`.
  - `diff_down[w]`: Difference between the maximum and minimum occurrences of colours in column `w`.
- **Objective**:
  - Minimise the maximum difference across all rows and columns:
    \[
    \text{objective} = \max(\text{diff_across} \cup \text{diff_down})
    \]
  - This ensures a balanced colour distribution.

---

## Symmetry Breaking

- Colours are interchangeable, so a `value_precede_chain` constraint is used to reduce symmetric solutions.

---

## Output

The solution is a grid where:

- Each row and column contains all colours in contiguous blocks.
- Colour distribution is as balanced as possible.

---

### References

- Inspired by artistic puzzle concepts discussed in [Irregular Mondoku Art](https://www.reddit.com/r/generative/comments/1fxp5ng/irregular_mondoku_art/).
- Model by Mikael Zreleased under MIT License.
