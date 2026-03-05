# Generalized Peaceable Queens

## Overview

This MiniZinc model solves the **Generalized Peaceable Queens Problem**. The problem is defined on an `n × n` chessboard with `q` different armies (or colours) of queens. The goal is to **maximize the number of queens placed on the board** such that:

- Queens from **different armies do not attack each other**.
- All armies have **equal size** (same number of queens).

This is a generalisation of the classic Peaceable Queens problem, which typically involves two armies (black and white). For `q = 2`, known optimal solutions are documented in [OEIS A250000](https://oeis.org/A250000).

---

## Problem Description

- A chessboard of size `n × n`.
- `q` armies of queens (e.g., black, white, purple, etc.).
- Queens attack along rows, columns, and diagonals as in standard chess.
- Queens of the **same army may attack each other**, but queens of **different armies must not**.

The challenge is to place as many queens as possible under these conditions.

---

## Key Parameters

- `n`: Size of the chessboard.
- `q`: Number of armies (colours).
- `Armies`: Enumeration of armies (`Army(1..q)`).
- `Squares`: Possible states for each square (`EMPTY` or `Q(Army)`).

---

## Decision Variables

- `x[i,j]`: Represents the state of square `(i,j)`:

  - `EMPTY` if no queen is placed.
  - `Q(Army)` if occupied by a queen of a specific army.

- `counts[a]`: Number of queens for each army `a`.

- `objective`: The size of each army (since all armies must be equal, this is the number of queens per army).

---

## Constraints

1. **Non-Attacking Across Armies**:

   - Queens from different armies cannot share a row, column, or diagonal.
   - Implemented using a **regular constraint** that ensures each line (row, column, diagonal) contains queens from at most one army.

2. **Equal Army Sizes**:

   - All armies have the same number of queens (`all_equal(counts)`).

3. **Global Cardinality**:

   - Counts the number of squares occupied by each army.

4. **Symmetry Breaking**:
   - Removes equivalent solutions caused by board rotations/reflections.
   - Prevents arbitrary swapping of armies.

---

## Objective

Maximise:
\[
\text{objective} = \text{counts}[Q(\text{Armies}[1])]
\]
This represents the number of queens per army, ensuring all armies are equally large.

---

## Output

The solution prints:

- The chessboard layout (`.` for empty squares, letters for armies).
- Board size `n`, number of armies `q`.
- Counts of queens per army.
- Objective value.

---

## References

- Smith et al., _Constraint Programming for Peaceable Queens_, CP 2004.
- [OEIS A250000](https://oeis.org/A250000) for optimal solutions when `q = 2`.
