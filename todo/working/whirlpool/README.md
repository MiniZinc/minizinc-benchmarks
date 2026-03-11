# Whirlpool (extended, perfect diagonal) — beginner-friendly model guide

## What problem is this model solving?
This MiniZinc model encodes a **number arrangement puzzle** on an \(n \times n\) grid.

You must place all numbers from \(1\) to \(n^2\), each exactly once, so that:
- every local \(2 \times 2\) block has a consistent clockwise or counterclockwise “whirlpool” order,
- each concentric ring (outer border, then next inner border, etc.) also follows that whirlpool ordering,
- and both main diagonals have a prescribed “perfect diagonal” sum.

The model is a **satisfaction problem** (`solve ... satisfy`): it looks for any arrangement meeting all rules, rather than maximizing/minimizing something.

## Core decision variables
- `int: n;` — puzzle size.
- `int: m = n;` — number of rows (fixed equal to columns, so the board is square).
- `array[ROW,COL] of var 1..m*n: x;` — the grid values.
  - Each `x[i,j]` is an integer in `1..n^2`.
  - `alldifferent(x)` forces a permutation of `1..n^2` across the whole grid.

## Key modeling idea: the `whirlpool(...)` predicate
The predicate takes a sequence and counts how many adjacent pairs are increasing:

\[
\sum_{i=1}^{k} [x_i < x_{i+1}] \in \{1, k-1\}
\]
(with wrap-around from last back to first).

Interpretation:
- `k-1` increases means the sequence is almost entirely increasing around the cycle,
- `1` increase means the reverse orientation.

So this is a compact way to allow **either clockwise or counterclockwise cyclic order**.

## Constraints in plain language
1. **All numbers are unique**
   - `alldifferent(x)`.

2. **Every 2×2 sub-square is a whirlpool**
   - For each `i=1..n-1`, `j=1..n-1`, apply `whirlpool` to
     `[x[i,j], x[i,j+1], x[i+1,j+1], x[i+1,j]]`.

3. **Every concentric ring is a whirlpool**
   - For each layer `k`, build the border cycle of that layer (top row, right column, bottom row reversed, left column reversed) and enforce `whirlpool(...)`.

4. **Perfect diagonal sums**
   - Main diagonal: `sum(i in 1..n)(x[i,i]) = n*(n+1)*(n+1) div 2`.
   - Anti-diagonal: `sum(i in 1..n)(x[i,n+1-i]) = n*(n+1)*(n+1) div 2`.

## Objective
- **No optimization objective is present.**
- This is a feasibility/SAT model: find any valid grid.

## Output
The solver prints the solution as:
- `x = array2d(ROW, COL, x);`
which is easy to post-process or inspect.

## Uncertainty / caveats
- The comments describe “perfect diagonal whirlpool permutation” and give the diagonal-sum formula, but they do not provide a full external formal definition in this file.
- The ring construction is concise and index-heavy; this explanation reflects the intended layer traversal visible in the code.
- The model assumes square grids (`m = n`), so any broader rectangular variant (if it exists in literature) is not represented here.

## Identifiable references
- Model source in this repository: `todo/working/whirlpool/whirlpool-x.mzn`.
- Repository metadata (classification/challenge info): `todo/working/whirlpool/metadata.json` (type: puzzle, kind: sat, challenge year listed as 2020).
- No external paper/URL reference is explicitly embedded in the model file or metadata.
