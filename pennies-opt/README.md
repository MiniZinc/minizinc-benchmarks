# MiniZinc Model: Distinct Distances for Pennies on a Chessboard

## **Overview**

This model tackles the problem of placing pennies on an **n × n chessboard** such that:

- All pennies occupy distinct squares.
- The squared distances between every pair of pennies are **unique**.
- The goal is to **maximise the number of pennies** placed under these conditions.

The problem is inspired by a computational complexity challenge discussed https://blog.computationalcomplexity.org/2023/06/can-you-put-n-pennies-on-n-x-n.html.

---

## **Problem Description**

- **Board Size:** `n × n`.
- **Objective:** Place as many pennies as possible so that:
  - No two pennies share the same square.
  - All pairwise distances are distinct (using squared Euclidean distance for integrality).

---

## **Variables**

- `int: n`  
  Size of the chessboard.
- `set of int: N = 1..n`  
  Row and column indices.
- `array[N] of var bool: is_present`  
  Indicates whether a penny is placed.
- `array[N] of var opt N: x`  
  X-coordinate of each penny (optional).
- `array[N] of var opt N: y`  
  Y-coordinate of each penny (optional).
- `array[N] of var opt NN: xy`  
  Combined position index for each penny.
- `var N: pennies`  
  Total number of pennies placed.
- `array[int] of var opt int: distances`  
  Squared distances between pairs of pennies (optional values for absent pennies).

---

## **Constraints**

1. **Unique Positions:**  
   Each penny occupies a distinct square:

   ```minizinc
   constraint all_different(xy);
   ```

2. **Unique Distances:**  
   All pairwise distances must be different:

   ```minizinc
   constraint all_different(distances);
   ```

3. **Position Linking:**  
   Connect `x`, `y`, and `xy` variables:

   ```minizinc
   xy[i] = ((x[i]-1) * n) + (y[i]-1);
   ```

4. **Presence Consistency:**  
   A penny is present if its coordinates and position are assigned:

   ```minizinc
   is_present[i] = occurs(x[i]) /\ occurs(y[i]) /\ occurs(xy[i]);
   ```

5. **Symmetry Breaking:**

   - Enforce ordering of positions to reduce equivalent solutions.
   - Ensure `is_present` is in decreasing order.

6. **Count Pennies:**
   ```minizinc
   pennies = sum(is_present);
   ```

---

## **Objective**

Maximise the number of pennies placed:

```minizinc
solve maximize pennies;
```

---

## **Output**

- A visual representation of the board showing penny placements.
- List of distances between pennies.
- Coordinates of pennies (`x` and `y`).
- Total number of pennies placed.

---

## **Applications**

- Geometric optimisation problems.
- Combinatorial design and packing problems.
- Educational puzzles in discrete mathematics.

---

## **References**

- Mikael Zayenz Lagerkvist (Model Author).
- Related discussion: <https://blog.computationalcomplexity.org/2023/06/can-you-put-n-pennies-on-n-x-n.html>.

---
