# Nonogram

## Problem Description

A **Nonogram** (also known as _Picross_, _Paint by Numbers_, or _Griddler_) is a classic logic puzzle played on a rectangular grid. The goal is to determine which cells in the grid should be filled in (coloured) and which should be left empty, based on numerical clues provided for every row and every column.

Each clue for a row or column is a sequence of positive integers. These integers describe the lengths of consecutive **runs** of filled cells in that row or column, in order from left to right (for rows) or top to bottom (for columns). For example, a clue of `[3, 1]` means there is a run of exactly 3 filled cells followed (after at least one empty cell) by a run of exactly 1 filled cell. There must be at least one empty cell between any two consecutive runs.

Nonograms are well-known combinatorial puzzles that have been studied extensively in constraint programming and artificial intelligence. They were independently invented by Non Ishida and Tetsuya Nishio in Japan in 1987. The problem is NP-complete in general.

## Model Parameters

| Parameter | Description                                                                                                                                       |
| --------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| `X`       | The number of columns in the grid                                                                                                                 |
| `Y`       | The number of rows in the grid                                                                                                                    |
| `maxlen`  | The maximum number of clue entries for any single row or column                                                                                   |
| `rows`    | A 2D array of size `Y × maxlen` giving the run-length clues for each row. A value of `0` (or negative) indicates a padding entry with no meaning. |
| `cols`    | A 2D array of size `X × maxlen` giving the run-length clues for each column. Padding is handled the same way as for rows.                         |

## Decision Variables

| Variable | Domain                          | Description                                                             |
| -------- | ------------------------------- | ----------------------------------------------------------------------- |
| `A`      | `array[1..Y, 1..X] of var 1..2` | The grid itself. Each cell takes the value `1` (empty) or `2` (filled). |

## Constraints

The model enforces two sets of constraints:

- **Row constraints**: For each row `i`, the sequence of cells `A[i, 1], A[i, 2], ..., A[i, X]` must match the run-length clue given by `rows[i, ...]`.
- **Column constraints**: For each column `j`, the sequence of cells `A[1, j], A[2, j], ..., A[Y, j]` must match the run-length clue given by `cols[j, ...]`.

Each individual row or column constraint is enforced using the `nonogram` predicate, which internally uses the MiniZinc global constraint `regular`. The `regular` constraint checks that a sequence of variables corresponds to a word accepted by a finite automaton (a DFA). The model constructs the DFA transition table on-the-fly from the clue sequence using two small lookup arrays (`nonmul` and `nonadd`) that encode how DFA states should transition depending on consecutive clue values.

## Objective

This is a **satisfaction** problem — there is no objective function to minimise or maximise. The goal is simply to find a valid assignment of the grid cells that satisfies all row and column clues simultaneously.

## Output

The solution is printed as a grid of characters:

- `.` represents an empty cell (value `1`)
- `x` represents a filled cell (value `2`)

> **Note**: The output section iterates over indices `r in 1..X` and `c in 1..Y`, which appears to be transposed relative to the logical row/column orientation of the grid (`A` is declared as `array[1..Y, 1..X]`). If the puzzle output looks transposed, this may be the cause, and an expert review of the output section is recommended.

## References

- Batenburg, K.J., & Kosters, W.A. (2009). _Solving Nonograms by combining relaxations_. Pattern Recognition, 42(8), 1672–1683.
- Wiggers, W. (2004). _A comparison of approaches to solving nonograms_. Proceedings of the 16th Belgium-Netherlands Artificial Intelligence Conference (BNAIC 2004).
- Ueda, N., & Nagao, T. (1996). _NP-completeness results for Nonogram via Parsimonious Reductions_. Technical Report TR96-0008, Tokyo Institute of Technology.
- Simpson, G. (1987–). The puzzle was independently created by Non Ishida and Tetsuya Nishio in Japan and popularised under the name _Nonogram_ / _Picross_.
