# Hitori (Optimisation)

## Problem Description

**Hitori** is a classic Japanese logic puzzle played on an $n \times n$ grid. Each cell in the grid contains a number between 1 and $n$. The goal is to decide which cells to "black out" (shade) so that three rules are satisfied simultaneously:

1. **Uniqueness**: In every row, the unshaded numbers must all be different. Likewise for every column.
2. **No adjacency**: No two shaded cells may touch each other horizontally or vertically.
3. **Connectivity**: All unshaded cells must form a single connected region (i.e., you can travel between any two unshaded cells by moving horizontally or vertically through other unshaded cells).

The standard puzzle asks for a feasible solution. This model formulates an **optimisation variant**: it seeks a valid Hitori solution that **maximises the total sum of the numbers in the shaded cells**.

A reference for the standard Hitori puzzle can be found at [puzzle-hitori.com](https://www.puzzle-hitori.com/).

## Input Parameters

| Parameter | Type                        | Description                                       |
| --------- | --------------------------- | ------------------------------------------------- |
| `n`       | `int`                       | The side length of the square grid.               |
| `clue`    | `array[1..n, 1..n] of 1..n` | The number pre-filled in each cell of the puzzle. |

## Decision Variables

| Variable      | Type       | Description                                                                                                                                                      |
| ------------- | ---------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `filled[r,c]` | `var bool` | `true` if cell $(r,c)$ is shaded (blacked out), `false` if it remains unshaded.                                                                                  |
| `x[r,c]`      | `var 0..n` | The effective value of cell $(r,c)$: equals the clue value when the cell is unshaded, or 0 when the cell is shaded. Used to enforce the uniqueness constraints.  |
| `edge[e]`     | `var bool` | An auxiliary variable for each potential edge in the grid graph. An edge is "active" when both of its endpoint cells are unshaded. Used to enforce connectivity. |

## Constraints

### Uniqueness (rows and columns)

For each row and each column, the non-zero entries of `x` (i.e., the unshaded cells) must all be different. This is enforced with the `alldifferent_except_0` global constraint.

### No adjacent shading

Two horizontally or vertically neighbouring cells cannot both be shaded.

### Connectivity

The unshaded cells must form a single connected component. This is modelled explicitly using a graph where nodes are cells and edges connect horizontally or vertically adjacent cells. Only edges between two unshaded cells are active. The `connected` predicate (defined in the model itself, as a `test` rather than a `constraint`, to support solution checking) verifies that all unshaded nodes are reachable from a common root.

### Propagation / implied constraints

The model also includes several additional constraints that help narrow the search without changing the set of feasible solutions:

- A cell whose clue value is unique in its row **and** unique in its column can never be shaded (commented out in the model but noted).
- If two adjacent cells in a row (or column) share the same clue value, then any other cell in that row (or column) with the same value must be shaded.
- A cell sandwiched between two cells with the same clue value (e.g., `… 3 ? 3 …`) cannot be shaded, because shading it would disconnect the two identical neighbours.
- Special-case corner rules are applied for the four corners of the grid.

## Objective

$$\text{maximise} \quad \sum_{r,c} \mathtt{filled}[r,c] \times \mathtt{clue}[r,c]$$

The model maximises the sum of the clue values of all shaded cells. This turns Hitori from a pure feasibility puzzle into a combinatorial optimisation problem.

## Output

The model prints the grid, showing each unshaded cell's number and replacing shaded cells with a block of `#` characters. It also reports:

- `obj`: the value of the objective (total shaded-cell sum achieved).
- `nofilled`: the number of shaded cells in the solution.

## Notes

- The connectivity predicate is implemented as a recursive MiniZinc `test`/`function` rather than using a built-in global, which may affect solver performance on larger instances.
- The optimisation direction (maximise shaded-cell sum) is an unusual variant; most Hitori benchmarks only test feasibility. It is unclear from the model alone whether this specific objective is taken from a published paper or is an original contribution — a domain expert should verify this.
