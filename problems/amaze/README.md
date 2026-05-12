# Amaze (Numberlink / Flow Free)

## Problem Description

The **Amaze** puzzle (also known as **Numberlink** or **Flow Free**) is a logic puzzle played on a rectangular grid. The grid contains a set of numbered endpoint pairs — for example, two cells both labelled "1", two cells both labelled "2", and so on. The goal is to connect each pair of matching numbers by drawing a continuous path that travels only horizontally or vertically (never diagonally). Paths must not cross or share any cell.

This is a well-known combinatorial puzzle that appears frequently in puzzle books and mobile games. The model minimises a weighted measure of total path length (described below).

## Grid and Parameters

| Parameter                                        | Meaning                                           |
| ------------------------------------------------ | ------------------------------------------------- |
| `X`                                              | Width of the grid (number of columns)             |
| `Y`                                              | Height of the grid (number of rows)               |
| `N`                                              | Number of endpoint pairs to connect               |
| `end_points_start_x[n]`, `end_points_start_y[n]` | Column and row of the first endpoint of pair `n`  |
| `end_points_end_x[n]`, `end_points_end_y[n]`     | Column and row of the second endpoint of pair `n` |

## Decision Variables

The central decision variable is:

- **`board[x, y]`** — an integer variable for every cell `(x, y)` in the grid (with a one-cell border of zeros added around the outside to simplify boundary handling). A value of `0` means the cell is empty; a value of `n` (where `1 ≤ n ≤ N`) means the cell is part of the path connecting endpoint pair `n`.

## Constraints

1. **Boundary is empty** — all cells in the added border around the grid are fixed to `0`.

2. **Endpoints are placed** — for each pair `n`, the two given endpoint cells are assigned value `n` on the board.

3. **Endpoints have exactly one same-valued neighbour** — each endpoint cell (the start and end of a path) must have exactly one horizontal or vertical neighbour carrying the same path number. This captures the fact that a path has two loose ends, each of which connects to exactly one next cell.

4. **Interior path cells have exactly two same-valued neighbours** — any non-empty, non-endpoint cell must have exactly two horizontal or vertical neighbours with the same value. This enforces that the path passes through such a cell (entering from one side and exiting from another), forming a continuous, non-branching route.

Together, constraints 3 and 4 ensure that each path forms a simple (non-branching, non-looping) chain from one endpoint to the other.

## Objective

The model **minimises the sum of all cell values** on the board:

$$\text{minimise} \sum_{x,y} \texttt{board}[x, y]$$

Because each cell belonging to path `n` contributes `n` to the sum, this is a weighted sum that penalises longer paths for higher-numbered pairs more heavily. In practice it tends to find solutions where paths are as short as possible overall, though the weighting by path index means it is not a pure minimisation of total path length.

> **Note:** The exact motivation for this particular objective (rather than, say, counting the total number of filled cells) is not immediately clear from the model. A pure coverage minimisation would use a 0/1 indicator per cell. Anyone familiar with the original problem source may wish to clarify this.

## Example

On a 5×5 grid with two pairs:

```
. . . . .
. 1 . 2 .
. . . . .
. 1 . 2 .
. . . . .
```

A valid solution connects each `1` to the other `1` and each `2` to the other `2` without the paths touching.

## References

- Numberlink puzzle overview: [Wikipedia — Numberlink](https://en.wikipedia.org/wiki/Numberlink)
- The puzzle is also marketed commercially as **Flow Free** by Big Duck Games.
- For a constraint programming treatment of similar path/connection puzzles, see: Trick, M. (2001). _A Dynamic Programming Approach for Consistency and Propagation for Knapsack Constraints_. CPAIOR. (General CP puzzle solving techniques.)

## Model update summary

Added concise inline comments in amaze.mzn to clarify:

- board variable semantics (`0` empty, `1..N` path identifiers),
- endpoint/interior path interpretation,
- objective meaning as weighted path compactness.
