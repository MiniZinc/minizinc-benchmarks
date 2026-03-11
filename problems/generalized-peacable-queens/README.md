# Generalized Peaceable Queens

## Problem Description

The **Generalized Peaceable Queens** problem places chess queens of multiple "armies" (colors) on an _n × n_ chessboard such that:

1. Queens from **different armies never attack each other** — no two queens from different armies share the same row, column, or diagonal.
2. Every army has **exactly the same number of queens**.
3. The **total number of queens** placed on the board (equivalently, the size of each army) is **maximized**.

The classic version of this problem uses two armies (e.g., black and white queens). This model generalizes it to any number `q` of armies. For the two-army case, all known optimal solutions are catalogued on [OEIS A250000](https://oeis.org/A250000).

## Parameters

| Parameter | Description                                   |
| --------- | --------------------------------------------- |
| `n`       | The size of the chessboard (an _n × n_ grid). |
| `q`       | The number of armies (colors of queens).      |

## Decision Variables

| Variable  | Description                                                                                                                                                                                                                                  |
| --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `x[i, j]` | For each square `(i, j)` on the board, this variable records whether the square is **empty** or occupied by a queen from a particular army. Its value is one of: `EMPTY`, or an army identifier `Q(Army(1))`, `Q(Army(2))`, …, `Q(Army(q))`. |

## Constraints

- **Row peace**: Within any single row, all queens must belong to the same army (or the row may contain queens of only one army mixed with empty squares). Queens from two different armies may not share a row.
- **Column peace**: The same rule applies to every column.
- **Diagonal peace**: The same rule applies to every diagonal in both directions.
- **Equal army sizes**: Every army must have the same number of queens on the board.

The "peace" constraints are modelled using a regular (automaton/DFA) constraint. Each row, column, and diagonal is treated as a sequence of squares; the automaton accepts only sequences that contain at most one distinct army's queens.

## Objective

Maximize `objective`, which equals the number of queens in each army. Since all armies are required to be the same size, maximizing one army's count maximizes all of them simultaneously (and hence the total number of queens on the board).

## Symmetry Breaking

The model includes symmetry-breaking constraints to reduce the search space:

- **Geometric symmetry**: The chessboard has 8 symmetries (4 rotations and 4 reflections). The model enforces that the lexicographically smallest representative is chosen.
- **Army permutation symmetry**: Relabelling which army is called "army 1" vs "army 2" etc. produces equivalent solutions. A value-precedence constraint ensures armies are assigned labels in the order they first appear on the board.

## Output

The solved board is printed with `.` for empty squares and a letter (`A`, `B`, `C`, …) representing the army of the queen on each occupied square. Summary statistics (`n`, `q`, army counts, and the objective value) are also printed.

## References

- Bierlee, H. (2022). _Generalized Peaceable Queens_ (MiniZinc model). Licensed under the MIT License.
- Smith, B. M., Stergiou, K., & Walsh, T. (2004). _Modelling the Peaceable Queens Problem_. Workshop on Constraint Modelling and Reformulation, CP 2004.
- OEIS Foundation. _A250000: Peaceable Queens_. [https://oeis.org/A250000](https://oeis.org/A250000)
