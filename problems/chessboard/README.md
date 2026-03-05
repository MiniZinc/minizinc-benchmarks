# Nontaking Armies on a Chessboard

## Overview

This MiniZinc model solves the **Nontaking Armies Problem**, where different chess pieces (knights, bishops, rooks, and queens) are placed on an `n × n` chessboard so that none can capture another. Each piece type has a specified limit on how many can be placed, and each piece has an associated value. The objective is to maximise the total value of the arrangement while respecting the non-attacking constraints.

---

## Problem Description

- **Chessboard**: An `n × n` grid.
- **Pieces**: Knights (N), Bishops (B), Rooks (R), Queens (Q), and empty squares (e).
- **Goal**: Place pieces on the board so that:
  - No two pieces can attack each other according to chess rules.
  - The number of each piece does not exceed its specified limit.
- **Objective**: Maximise the sum of the values of all placed pieces.

---

## Key Parameters

- `n`: Size of the chessboard.
- `value[p]`: Value assigned to each piece type `p`.
- `limit[p]`: Maximum number of pieces of type `p` allowed.
- `ROW`, `COL`: Sets representing rows and columns of the board.

---

## Decision Variables

- `x[r,c]`: The piece placed at row `r`, column `c` (from the set {N, B, R, Q, e}).
- `cnt[p]`: Count of pieces of type `p` on the board.
- `obj`: Total value of all placed pieces (objective to maximise).

---

## Constraints

1. **Global Cardinality**:
   - Tracks the number of each piece type on the board.
   - Ensures limits on piece counts are respected.
2. **Row and Column Rules**:
   - If a rook or queen is in a row or column, no other piece can share that line.
3. **Diagonal Rules**:
   - If a bishop or queen is on a diagonal, no other piece can share that diagonal.
4. **Knight Rules**:
   - Knights cannot attack any other piece (L-shaped moves).
5. **Redundant Constraints**:
   - Additional bounds on piece counts for efficiency.
6. **Symmetry Breaking**:
   - Removes symmetrical solutions by enforcing lexicographic ordering under rotations and reflections.

---

## Objective

Maximise:

$$
\text{obj} = \sum_{r \in ROW, c \in COL} \text{value}[x[r,c]]
$$

This ensures the arrangement of pieces yields the highest possible total value.

---

## Notes

- The model includes dominance rules to reduce search space based on piece values.
- Symmetry-breaking constraints handle rotations and reflections of the board.
- This problem is related to combinatorial optimisation and chess puzzle design.

---

### References
