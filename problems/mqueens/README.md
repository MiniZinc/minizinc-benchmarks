# Minimum Dominating Queens (mqueens)

## Problem Description

This model solves the **minimum dominating queens** problem on an $n \times n$ chessboard. The goal is to place the fewest possible non-attacking queens such that every square on the board is either occupied by a queen or attacked (threatened) by at least one queen.

A queen attacks all squares in the same row, column, and diagonals.

This is distinct from the classic $n$-Queens problem (which places exactly $n$ non-attacking queens, one per row). Here, we want to find the _smallest_ set of queens that collectively "covers" the entire board, while still ensuring no two queens attack each other.

This problem is equivalent to finding a **minimum independent dominating set** on the queens graph, where:

- **Independent**: No two queens attack each other.
- **Dominating**: Every square not occupied by a queen is attacked by at least one queen.

This is a well-studied combinatorics problem. Related work can be found in:

- Burger, A.P., Cockayne, E.J., & Mynhardt, C.M. (1997). _Domination and irredundance in the queens' graph_. Discrete Mathematics, 163(1–3), 47–66.
- Weakley, W.D. (2002). _Domination in the queen's graph_. Graph Theory, Combinatorics, and Algorithms.

## Parameters

| Name | Type  | Description                               |
| ---- | ----- | ----------------------------------------- |
| `n`  | `int` | The size of the chessboard ($n \times n$) |

## Variables

| Name          | Type              | Description                                                                       |
| ------------- | ----------------- | --------------------------------------------------------------------------------- |
| `filled[i,j]` | `bool` (per cell) | `true` if a queen is placed at row `i`, column `j`; `false` otherwise             |
| `f[i,j]`      | `0..1` (per cell) | Integer equivalent of `filled[i,j]` (0 or 1), used in sum expressions             |
| `q[i]`        | `0..n` (per row)  | The column position of the queen in row `i`, or `0` if row `i` has no queen       |
| `objective`   | `0..n`            | The number of rows that contain a queen (i.e., the total number of queens placed) |

## Model update summary

Added concise inline comments in `mqueens2.mzn` to clarify:

- the queen placement variables (`filled`, `f`, `q`) and what they represent,
- the objective variable counting the total number of queens placed,
- the symmetry-breaking predicates and their role in reducing search space.

## Constraints

### Domination and independence (main constraint)

The core constraint encodes both the independence and domination conditions simultaneously:

> A cell `(i,j)` is occupied by a queen **if and only if** no other filled cell exists in the same row, same column, or any diagonal through `(i,j)`.

This is a self-referential (fixed-point) constraint. It enforces:

- **Independence**: A queen at `(i,j)` means no other queen attacks it.
- **Domination**: An empty cell `(i,j)` means at least one queen exists that attacks it.

### Row queen position

`q[i]` is computed as the (weighted) sum of filled cells in row `i`. Because the independence constraint ensures at most one queen per row, `q[i]` equals the column of the queen in row `i`, or `0` if no queen is placed in row `i`.

### Symmetry breaking

A rotational symmetry-breaking constraint (`rot_sqr_sym`) is applied to the board to reduce the search space. This eliminates solutions that are equivalent under 90°, 180°, and 270° rotations of the board.

> **Note for experts**: The symmetry-breaking predicate uses `var_perm_sym` and `var_perm_sym_pairwise`, which enforce lexicographic ordering between permuted views of the flattened board. This is a relatively advanced technique and may be worth verifying for correctness and tightness.

## Objective

The model **minimises** `objective`, which counts the number of rows that contain a queen. Since the independence constraint allows at most one queen per row, this is equivalent to minimising the total number of queens placed on the board.

## Output

The model outputs:

- `q`: the column position of the queen in each row (0 if the row is empty).
- `objective`: the minimum number of queens needed to dominate the board.
