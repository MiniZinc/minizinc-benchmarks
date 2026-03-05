# Hitori Puzzle Model

## Overview

This MiniZinc model solves the **Hitori puzzle**, a logic-based grid puzzle. The puzzle consists of an `n × n` grid filled with numbers. The goal is to shade (black out) some cells so that:

1. No number appears more than once in any row or column among the unshaded cells.
2. Shaded cells do not touch each other horizontally or vertically.
3. All unshaded cells remain connected (form a single connected group).

The model enforces these rules and finds a solution that maximises a given objective.

---

## Problem Description

- **Input**:

  - `n`: Size of the square grid.
  - `clue[r,c]`: The number in row `r`, column `c` (values from 1 to `n`).

- **Output**:
  - A grid showing which cells are shaded (represented by `#`) and which remain visible (showing their number).
  - Additional statistics such as the number of shaded cells and the objective value.

---

## Decision Variables

- `filled[r,c]`: Boolean variable indicating whether cell `(r,c)` is shaded (`true`) or not (`false`).
- `x[r,c]`: The value in cell `(r,c)` if it is not shaded, otherwise `0`.

---

## Constraints

1. **Uniqueness**:

   - All non-shaded numbers in each row and column must be unique.
   - Implemented using `alldifferent_except_0` on rows and columns.

2. **Adjacency**:

   - No two shaded cells can be adjacent horizontally or vertically.

3. **Connectivity**:

   - All non-shaded cells must form a single connected region.
   - Achieved using a custom `connected` predicate that checks reachability.

4. **Logical Deductions**:
   - If two identical clues are adjacent, other identical clues in that row/column must be shaded.
   - A cell between two identical cells cannot be shaded.
   - Special corner cases are handled explicitly.

---

## Objective

The model **maximises**:
\[
\text{obj} = \sum\_{\text{shaded cells}} (\text{clue value})
\]
This means the solution prefers shading cells with higher numbers, while still satisfying all puzzle rules.

---

## Output

- The final grid with shaded cells marked as `#`.
- Objective value (`obj`).
- Number of shaded cells (`nofilled`).

---

## Notes

- This model uses global constraints like `alldifferent_except_0` and custom connectivity checks.
- It is based on the rules of the Hitori puzzle as described on [puzzle-hitori.com](https://www.puzzle-hitori.com/).
- The search strategy focuses on finding a valid configuration that maximises the objective.

---
