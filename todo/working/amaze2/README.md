# Amaze 2 — Grid Path Routing

## Problem Description

This model solves a **grid path-routing puzzle** (sometimes called a "wire routing" or "Numberlink-style" problem). Given a rectangular grid and a set of **N pairs of endpoints**, the task is to find N non-overlapping paths on the grid such that each path connects one designated start cell to its corresponding end cell.

Each cell in the grid may be used by at most one path, and unused cells are left empty. Paths may only move horizontally or vertically between adjacent cells (no diagonal moves).

This type of puzzle is closely related to the well-known **Numberlink** pencil puzzle, where numbered pairs of cells must be connected by non-crossing paths. The "amaze" family of benchmarks has been used in constraint programming competitions, including the MiniZinc Challenge.

## Parameters

| Parameter                                  | Description                                         |
| ------------------------------------------ | --------------------------------------------------- |
| `X`                                        | Number of columns in the grid                       |
| `Y`                                        | Number of rows in the grid                          |
| `N`                                        | Number of endpoint pairs to connect                 |
| `end_points_start_x`, `end_points_start_y` | X and Y coordinates of the start cell for each pair |
| `end_points_end_x`, `end_points_end_y`     | X and Y coordinates of the end cell for each pair   |

## Derived Data

| Name           | Description                                                        |
| -------------- | ------------------------------------------------------------------ |
| `M`            | Total number of cells (`X * Y`)                                    |
| `id`           | A 2D array mapping grid coordinates to a unique cell number (1..M) |
| `neighbours`   | For each cell, the set of adjacent cells (up, down, left, right)   |
| `start`, `end` | For each pair, the cell IDs of the start and end endpoints         |

## Decision Variables

| Variable     | Domain | Description                                                                                                                                         |
| ------------ | ------ | --------------------------------------------------------------------------------------------------------------------------------------------------- |
| `path[0..M]` | `0..N` | For each cell, which pair's path passes through it. A value of `0` means the cell is not used by any path. `path[0]` is a dummy entry fixed to `0`. |
| `next[1..M]` | `0..M` | For each cell, the ID of the **next** cell along the path heading toward the end point. A value of `0` means the cell is unused.                    |

Together, `path` and `next` encode a set of directed chains across the grid, one per pair.

## Constraints

1. **Endpoint ownership**: The start and end cells of each pair are assigned to that pair in `path`.
2. **End cell is a terminal**: The `next` pointer of an end cell points back to itself, marking it as the path terminus.
3. **No incoming flow at start cells**: No neighbour of a start cell points _into_ it, making it a source rather than an intermediate node.
4. **Path ownership propagates**: For every non-end cell that is in use, its `next` cell belongs to the same pair.
5. **Single incoming neighbour**: Every active non-start cell has exactly one neighbour whose `next` pointer points to it, forming a simple (non-branching) chain.
6. **Unused cells are inactive**: If a cell is not assigned to any path (`path = 0`), its `next` is also `0`.

## Objective

This is a **satisfaction** problem — there is no objective function to minimise or maximise. The solver simply searches for any assignment of `path` and `next` that satisfies all the constraints above.

## Output

The solution is displayed as a grid. Each cell prints the index of the pair whose path passes through it, or `0` for an empty cell, making it easy to visualise the routing.

## Notes

- The model does **not** require paths to cover every cell in the grid; cells can be left unrouted.
- The "amaze" name and benchmark instances have been used in the MiniZinc Challenge. If you have a reference to the original paper or instance generator for this specific variant, please add it here.

## References

- MiniZinc Challenge benchmark suite: <https://www.minizinc.org/challenge/>
- Numberlink puzzle (context): Ueda, N. & Nagao, T. (1996). _NP-completeness results for NONOGRAM via parsimonious reductions_. (Related combinatorial puzzle literature.)
