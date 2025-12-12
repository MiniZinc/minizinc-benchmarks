# MiniZinc Model: Peaceable Queens Problem

## **Overview**

The Peaceable Queens problem is a variation of the classic chessboard puzzle. On an **n × n chessboard**, the goal is to **place the maximum number of black and white queens** such that:

- Queens of **opposite colours do not attack each other**.
- The number of black queens equals the number of white queens.

This problem is a well-known combinatorial optimisation challenge and is related to sequence A250000 in the [OEIS](https://oeis.org/A250000).

---

## **Problem Description**

- **Board Size:** `n × n`.
- **Queens:** Two sets (black and white).
- **Constraints:**
  - Queens of different colours cannot attack each other (no shared row, column, or diagonal).
  - Equal number of black and white queens.
- **Objective:** Maximise the number of queens placed under these conditions.

---

## **Variables**

- `int: n`  
  Size of the chessboard.
- `enum Square = {EMPTY, BLACK, WHITE}`  
  Represents the state of each square.
- `array[1..n, 1..n] of var Square: x`  
  The chessboard configuration.
- `var int: objective`  
  Number of black queens (equal to white queens).

---

## **Key Constraints**

1. **Non-attacking condition:**  
   Implemented using a **regular constraint** that enforces peace along rows, columns, and diagonals:
   ```minizinc
   constraint forall(i in 1..n)(
       at_peace(x[i,..]) /\ at_peace(x[..,i])
   );
   ```

Similar constraints apply to diagonals.

2.  **Equal number of black and white queens:**

    ```minizinc
    constraint objective == count(x_i_j in array1d(x))(x_i_j == WHITE);
    ```

3.  **Symmetry Breaking:**
    - Rotational and reflection symmetries of the board.
    - Colour symmetry (black ↔ white exchange).

---

## **Objective**

Maximise the number of black queens (and thus white queens):

```minizinc
solve maximize objective;
```

---

## **Output**

The solution prints:

- Board configuration (`B` for black, `W` for white, `.` for empty).
- Board size `n`.
- Objective value (number of queens).
- Known optimal value from OEIS for comparison.

---

## **References**

- Hendrik Bierlee (Model Author).
- Smith et al., CP'2004 for insights into the problem.
- [OEIS A250000](https://oeis.org/A250000) for known optimal solutions.

---
