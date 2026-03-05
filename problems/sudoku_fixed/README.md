# MiniZinc Model: Sudoku Solver

## **Overview**

This MiniZinc model solves **Sudoku puzzles** of size `n × n`. Sudoku is a popular logic-based puzzle where the objective is to fill a grid with numbers so that:

- Each row contains all numbers from 1 to `n` without repetition.
- Each column contains all numbers from 1 to `n` without repetition.
- Each sub-grid (region) contains all numbers from 1 to `n` without repetition.

The model supports standard Sudoku puzzles (e.g., 9×9) and generalised versions for any `n` that forms a square grid.

---

## **Problem Description**

- **Input:**

  - `n`: Size of the Sudoku grid (e.g., `n = 9` for a standard puzzle).
  - `fixed`: A 2D array representing the initial puzzle configuration. Each cell is either:
    - A fixed number (1..n) if given in the puzzle.
    - `opt` (optional) if the cell is empty.

- **Goal:** Fill the empty cells so that all Sudoku rules are satisfied.

---

## **Decision Variables**

- `array[1..n, 1..n] of var 1..n: x`  
  Represents the value in each cell of the Sudoku grid.

---

## **Constraints**

1. **Respect Fixed Cells:**  
   If a cell is pre-filled, its value remains unchanged:

   ```minizinc
   x[i, j] ~= fixed[i, j];
   ```

2. **Row and Column Uniqueness:**  
   Each row and column must contain distinct numbers:

   ```minizinc
   alldifferent([x[i, j] | j in 1..n]);
   alldifferent([x[j, i] | j in 1..n]);
   ```

3. **Region Uniqueness:**  
   Each sub-grid (region) must contain distinct numbers:
   ```minizinc
   alldifferent([x[r, c] | r in i*reg+1..i*reg+reg, c in j*reg+1..j*reg+reg]);
   ```
   Here, `reg = ceil(sqrt(n))` determines the size of each region.

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

This means the goal is to **find any valid solution** that satisfies all Sudoku constraints.

---

## **Output**

The solution prints the completed Sudoku grid in a readable format.

---

## **References**

- Original Sudoku model adapted from <http://www.gecode.org/gecode-doc-latest/sudoku_8cpp-source.html>.
- Additional instances available at: [Hakank's MiniZinc Sudoku problems](http://www.hakank.org/minizinc).

---
