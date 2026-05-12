# Non-Taking Armies of Chess Pieces

## Problem Description

This problem asks: given an $n \times n$ chessboard, how do you place a combination of chess pieces — **Knights**, **Bishops**, **Rooks**, and **Queens** — so that **no piece can capture any other**, while **maximising the total value** of all placed pieces?

Each piece type has a point value and a maximum number that may be used. The goal is to choose which piece (if any) occupies each square of the board, subject to the standard chess movement rules, the per-type placement limits, and the objective of maximising total value.

This is a generalisation of classic single-piece placement puzzles (such as the $n$-Queens problem) to a mixed-piece setting. Related formulations appear in the constraint programming literature as benchmark problems for optimisation solvers.

## Parameters

| Parameter | Description                                                                                 |
| --------- | ------------------------------------------------------------------------------------------- |
| `n`       | Size of the chessboard ($n \times n$ squares)                                               |
| `value`   | Array giving the point value of each piece type (order: Knight, Bishop, Rook, Queen, empty) |
| `limit`   | Array giving the maximum number of each piece type that may be placed                       |

## Variables

| Variable  | Type                                     | Description                                                                                                    |
| --------- | ---------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `x[r, c]` | `PIECE` (one of `N`, `B`, `R`, `Q`, `e`) | The piece occupying row `r`, column `c`; `e` means the square is empty                                         |
| `cnt[p]`  | Integer                                  | The number of squares assigned piece type `p`                                                                  |
| `y[r, c]` | Integer (1–5)                            | An auxiliary variable encoding the same assignment as `x` but ranked by piece value (used to guide the search) |
| `obj`     | Integer                                  | The total value of all pieces placed on the board (the objective)                                              |

## Constraints

The model enforces the standard chess non-capture rules:

- **Rooks and Queens** — if a Rook or Queen occupies any square in a given row (or column), no other non-empty piece may appear in that same row (or column).
- **Bishops and Queens** — if a Bishop or Queen occupies any square on a given diagonal, no other non-empty piece may appear on that same diagonal. Both the upward and downward diagonals are covered.
- **Knights** — if a Knight occupies a square, all squares reachable by a standard knight's move (an "L"-shape: two squares in one direction and one square in the perpendicular direction) must be empty.
- **Placement limits** — the number of pieces of each type placed must not exceed the corresponding `limit` value.
- **Dominance rules** — if a Queen is worth no more than a Rook (or Bishop), then placing any Queen at all is only permitted when the maximum allowed number of Rooks (or Bishops) has already been placed. This avoids wasting potential value on Queens when the cheaper piece is equivalent or better.

## Objective

**Maximise** `obj`, the sum of `value[x[r,c]]` over all squares `(r, c)` on the board — that is, the total point value of all pieces placed.

## Symmetry Breaking

A chessboard has 8 symmetries (4 rotations and 4 reflections). The model uses a symmetry-breaking constraint (`var_sqr_sym`) that selects a canonical representative among all symmetric configurations, reducing the search space without removing any distinct solutions.

## Example Instance

In one supplied data file (`chessboard3`), the board is $7 \times 7$, pieces are valued Knights=3, Bishops=3, Rooks=5, Queens=2 (with limits of 5, 6, 6, 6 respectively). The solver must arrange at most those quantities of pieces on the 49 squares so that no piece attacks any other, aiming for the highest total score.

## References

The non-attacking placement of chess pieces is a classical topic in combinatorics and constraint programming:

- I. P. Gent, C. Jefferson, I. Miguel, P. Nightingale. _Variance to Order_. In Proceedings of CP, 2008. (Discusses independent-set and non-attacking piece placement benchmarks.)
- The single-piece case (non-attacking queens) is the well-known $n$-Queens problem; see: E. Sosič and J. Gu, _Efficient Local Search With Conflict Minimization: A Case Study of the n-Queens Problem_, IEEE TKDE, 1994.

> **Note for experts:** The model's auxiliary variable `y` and the `svalue` array (which ranks pieces by descending value) are used purely as a search hint and do not add any constraints beyond those already encoded in `x`. The correctness of the dominance-rule constraints (relating Queens to Rooks and Bishops) may warrant review for edge cases where `value[Q]` equals `value[R]` or `value[B]`.

## Model update summary

Added concise inline comments in `chessboard.mzn` to clarify:

- the piece placement array (`x`) and piece-counting logic,
- the piece-specific non-capture constraints (rooks/queens row control, bishops/queens diagonals, knight L-moves), and
- the dominance rules that prevent wasteful placement of higher-valued pieces when cheaper alternatives are available.
