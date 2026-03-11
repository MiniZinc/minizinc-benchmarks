# Amaze (Numberlink / Path-Connection Puzzle)

## Problem Description

The puzzle presents an `X` × `Y` grid in which `N` pairs of numbered endpoints are pre-placed at fixed cells. The task is to draw a non-intersecting path on the grid that connects each pair of endpoints, where each path is labelled with its pair number. Cells that are not part of any path are left empty (labelled `0`).

This is a combinatorial satisfaction problem — no objective function is minimised; the goal is simply to find any valid assignment of paths.

The puzzle is sometimes known as **Numberlink** or **Flow Free** in its commercial form. Instances used in this model were taken from the MiniZinc Challenge (2014 and 2019).

## Grid and Paths

- The grid has columns numbered `1..X` and rows numbered `1..Y`.
- There are `N` pairs of endpoints. For each pair `i`, one start cell and one end cell are given.
- A **path** for pair `i` is a sequence of adjacent (horizontally or vertically connected) cells, all labelled `i`, that forms an unbroken chain from the start endpoint to the end endpoint.
- Two paths may not share a cell — the labelling on the board uniquely identifies which path (if any) occupies each cell.

## Parameters

| Parameter               | Description                                          |
| ----------------------- | ---------------------------------------------------- |
| `X`                     | Number of columns in the grid                        |
| `Y`                     | Number of rows in the grid                           |
| `N`                     | Number of endpoint pairs (and thus paths) to connect |
| `end_points_start_x[i]` | Column of the start endpoint for pair `i`            |
| `end_points_start_y[i]` | Row of the start endpoint for pair `i`               |
| `end_points_end_x[i]`   | Column of the end endpoint for pair `i`              |
| `end_points_end_y[i]`   | Row of the end endpoint for pair `i`                 |

## Decision Variables

| Variable      | Description                                                                                                                                              |
| ------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `board[x, y]` | The label assigned to cell `(x, y)`. A value of `0` means the cell is unoccupied; a value of `i` (where `1 ≤ i ≤ N`) means the cell belongs to path `i`. |

## Constraints

1. **Endpoint placement** — The two endpoint cells for each pair `i` are fixed: `board[start_x[i], start_y[i]] = i` and `board[end_x[i], end_y[i]] = i`.

2. **Endpoints have exactly one path-neighbour** — Each endpoint cell has exactly one adjacent cell (horizontally or vertically) that carries the same label. This ensures the path enters (or leaves) the endpoint in only one direction, keeping the path a clean chain rather than a branching tree.

3. **Interior path cells have exactly two path-neighbours** — Any non-endpoint cell that carries a label `i > 0` must have exactly two adjacent cells with the same label. This forces every labelled non-endpoint cell to sit in the middle of a path (one predecessor, one successor), preventing loops or dead ends.

4. **Redundant bounding constraints** — For each pair `i`, if the two endpoints span multiple columns (or rows), then every intermediate column (or row) between them must contain at least one cell belonging to path `i`. This is a redundant constraint added to help the solver prune infeasible branches early; it does not change the set of solutions.

## Objective

This is a **satisfaction** problem — there is no quantity being minimised or maximised. Any assignment of `board` that satisfies all constraints is an accepted solution.

## Notes

- Cells left unoccupied (`board[x, y] = 0`) are permitted, so paths are not required to fill the entire grid. This distinguishes the model from some Numberlink variants that require full coverage.
- The instances in this benchmark were used in the MiniZinc Challenge in 2014 and 2019.

## References

- MiniZinc Challenge 2014: <https://www.minizinc.org/challenge2014/challenge.html>
- MiniZinc Challenge 2019: <https://www.minizinc.org/challenge2019/challenge.html>
- Numberlink puzzle (general description): Nikoli, _Numberlink_, <https://www.nikoli.co.jp/en/puzzles/numberlink/>
