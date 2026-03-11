# Triangular Hearts (MiniZinc Model Explanation)

## What problem is this model solving?

This model looks at an **equilateral triangular grid** with side length `n` and asks:

> How many points can we mark with a heart so that no three marked points form the corners of an equilateral triangle?

The forbidden equilateral triangle can be of **any size** and valid orientation on this grid.

So this is a **maximum packing** problem with a geometric restriction: place as many hearts as possible, but avoid creating any equilateral triangle from three hearts.

---

## Parameters and index sets

- `int: n;`  
  Size of the triangular grid (number of rows / side length).
- `set of int: N = 1..n;`  
  Row index set.

Although the array is declared as `n x n`, only the lower-triangular part (`j <= i`) is used as actual grid points.

---

## Decision variables

- `array [N, N] of var 0..1: heart;`  
  Binary variable for each potential grid location.
  - `heart[i,j] = 1` means a heart is placed at `(i,j)`.
  - `heart[i,j] = 0` means no heart.

- `var 1..n*n: objective;`  
  The total number of hearts placed.

The model links this variable with:

- `objective = sum(i in N, j in 1..i)(heart[i, j]);`

So only valid triangular-grid positions are counted.

---

## Core constraints

### 1) No equilateral triangle can be fully occupied

The main `forall(...)` constraint enumerates triples of positions that form equilateral triangles in the grid coordinate system. For each such triple, it enforces:

- `heart[a] + heart[b] + heart[c] <= 2`

This means at least one corner of every possible equilateral triangle must be empty.

### 2) Ignore cells outside the triangular region

Because `heart` is stored in a square array, entries with `j > i` are not real points of the triangular grid. The model forces these to zero:

- `heart[i, j] = 0` for all `j > i`.

---

## Objective

The solve goal is:

- **maximize `objective`**

So the solver searches for a placement with the largest possible number of hearts while satisfying the triangle-avoidance rule.

---

## Output format

The output prints:

1. `objective = ...;` (best number of hearts found),
2. the full square `heart` array,
3. then a triangular pretty-print (row 1 has 1 value, row 2 has 2, etc.).

This makes it easier to read the selected grid points visually.

---

## Notes and uncertainty

- The model comment says this puzzle is “Taken from Daily Telegraph and Sunday Times.” That suggests a puzzle-style origin rather than a formally cited research benchmark in this file.
- The variable comment says “Grid of equilateral triangulars,” which appears to mean “triangles / triangular grid points”; exact wording is slightly ambiguous but the model behavior is clear from constraints.
- This explanation is based only on `triangular.mzn`; no accompanying data file or publication metadata was provided in the same folder at the time of writing.

---

## Identifiable references

- In-file source note: *Daily Telegraph and Sunday Times* (as written in model comments).
- Model file: `triangular.mzn` in this directory.