# Sudoku Optimisation Model

## **Overview**

This MiniZinc model solves and optimises a **Sudoku puzzle**. Sudoku is a logic-based puzzle where the objective is to fill an `n × n` grid with numbers so that:

- Each row contains all numbers from 1 to `n` without repetition.
- Each column contains all numbers from 1 to `n` without repetition.
- Each sub-grid (region) contains all numbers from 1 to `n` without repetition.

Unlike a standard Sudoku solver, this model introduces an **optimisation objective** to find a solution that minimises a specific calculated value.

---

## **Problem Description**

- **Input:**

  - `n`: Size of the Sudoku grid (e.g., `n = 9` for a standard puzzle).
  - `fixed`: A 2D array representing the initial puzzle configuration. Each cell is either:
    - A fixed number (1..n) if given in the puzzle.
    - `opt` (optional) if the cell is empty.

- **Goal:** Fill the empty cells so that all Sudoku rules are satisfied and minimise the defined objective function.

---

## **Decision Variables**

- `array[1..n, 1..n] of var 1..n: x`  
  Represents the value in each cell of the Sudoku grid.
- `var -(n*n)..n*n: objective`  
  The optimisation variable, calculated based on the filled grid.

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

The model minimises:

```minizinc
objective = sum([x[i, j] * (-1)^(i + j) | i, j in 1..n]);
```

This creates an alternating sum of cell values based on their positions, adding an extra layer of complexity to the solution.

---

## **Output**

The solution prints the completed Sudoku grid in a readable format.

---

## **References**

- Original Sudoku model adapted from <http://www.gecode.org/gecode-doc-latest/sudoku_8cpp-source.html>.
- Additional instances available at: [Hakank's MiniZinc Sudoku problems](http://www.hakank.org/minizinc).

---
