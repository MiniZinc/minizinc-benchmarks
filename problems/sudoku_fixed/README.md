# Sudoku (Fixed Search)

## Problem Description

Sudoku is a classic logic puzzle played on an $n \times n$ grid, where $n$ is typically a perfect square (e.g., 9, 16, or 25). The grid is divided into $\sqrt{n} \times \sqrt{n}$ non-overlapping rectangular _regions_. Some cells are given a pre-filled value (the _clues_); the remaining cells must be filled in.

The goal is to place integers $1$ through $n$ into every cell such that:

- Each **row** contains every integer from $1$ to $n$ exactly once.
- Each **column** contains every integer from $1$ to $n$ exactly once.
- Each **region** (sub-grid of size $\sqrt{n} \times \sqrt{n}$) contains every integer from $1$ to $n$ exactly once.

This is a **satisfaction** problem — there is no objective to minimise or maximise; you simply need to find a valid assignment.

## Parameters

| Name    | Type                           | Description                                                                                       |
| ------- | ------------------------------ | ------------------------------------------------------------------------------------------------- |
| `n`     | `int`                          | Grid size. Must be a perfect square (e.g., 9, 16, 25).                                            |
| `board` | `array[1..n, 1..n] of opt int` | The initial puzzle. Each entry is either a fixed clue value (1–n) or `null` (unknown/empty cell). |

The use of _optional integers_ (`opt int`) allows `null` to represent an empty cell directly in the data file, without needing a special sentinel value like 0.

## Variables

| Name | Type                            | Description                                |
| ---- | ------------------------------- | ------------------------------------------ |
| `x`  | `array[1..n, 1..n] of var 1..n` | The value placed in each cell of the grid. |

Each `x[i, j]` ranges over $\{1, \ldots, n\}$. Cells that correspond to pre-filled clues are linked to their given value via `x[i,j] ~= board[i,j]` (the _optionally equal_ constraint, which is active only when `board[i,j]` is not absent/null).

## Constraints

1. **Clue propagation** — for every cell $(i, j)$ whose `board` entry is present, `x[i,j]` is forced to equal that clue value.
2. **Row uniqueness** — `alldifferent` over each row `x[i, 1..n]`.
3. **Column uniqueness** — `alldifferent` over each column `x[1..n, j]`.
4. **Region uniqueness** — `alldifferent` over each $\sqrt{n} \times \sqrt{n}$ sub-grid.

## Objective

None — this is a pure **satisfaction** (`solve satisfy`) model.

## Search Strategy

The model uses a fixed search annotation (`first_fail` variable selection, `indomain_split` value selection) applied to the flattened array of decision variables. The name _"sudoku_fixed"_ refers to this fixed search strategy. An alternative version using `dom_w_deg` (weighted degree) was the original; that annotation is commented out because `dom_w_deg` is not permitted in the MiniZinc Challenge.

> **Note on uncertainty:** The appropriateness of the fixed search strategy may vary across instances and solvers. Performance on very large grids (e.g., 25×25) could differ significantly from solving standard 9×9 instances.

## Instances

The benchmark data files (in `data/`) are 25×25 Sudoku puzzles drawn from a set of 91 instances originally distributed with the [Gecode](https://www.gecode.org/) constraint solver example `sudoku.cpp`. Five instances were used in the **MiniZinc Challenge 2023**:

- `sudoku_p20.json`, `sudoku_p26.json`, `sudoku_p28.json`, `sudoku_p48.json`, `sudoku_p89.json`

All 91 original instances are also available from Hakan Kjellerstrand's MiniZinc page.

## References

- Hakan Kjellerstrand, _MiniZinc models_, <http://www.hakank.org/minizinc>
- Original 91 puzzle instances: <http://www.hakank.org/minizinc/sudoku_problems2/>
- Gecode Sudoku example (source of the puzzle instances): <http://www.gecode.org/gecode-doc-latest/sudoku_8cpp-source.html>
- MiniZinc Challenge: <https://www.minizinc.org/challenge/>
