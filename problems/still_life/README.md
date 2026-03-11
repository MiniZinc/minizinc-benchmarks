# Still Life

## Problem Description

This problem is rooted in **Conway's Game of Life** — a famous cellular automaton where a grid of cells evolves over discrete time steps according to simple rules based on each cell's live neighbours:

- A cell with fewer than 2 live neighbours **dies** (underpopulation).
- A cell with exactly 2 live neighbours is **unchanged** in the next generation.
- A cell with exactly 3 live neighbours is **alive** in the next generation (birth or survival).
- A cell with more than 3 live neighbours **dies** (overpopulation).

A **still life** is a configuration of cells that is completely stable: it does not change at all from one generation to the next. The challenge here is not just to find _any_ still life, but the **densest possible one** — the arrangement of live cells on an $n \times n$ grid that maximises the number of live cells while remaining perfectly stable.

The grid is surrounded by an implicit border of permanently dead cells.

## Model Overview

### Parameters

| Name | Type  | Description                    |
| ---- | ----- | ------------------------------ |
| `n`  | `int` | Side length of the square grid |

### Variables

| Name        | Domain | Description                                               |
| ----------- | ------ | --------------------------------------------------------- |
| `a[r, c]`   | `0..1` | Whether cell $(r, c)$ is live (`1`) or dead (`0`)         |
| `s[r, c]`   | `0..6` | Number of live neighbours of cell $(r, c)$                |
| `objective` | `int`  | Total number of live cells (the quantity being maximised) |

The neighbour count `s[r, c]` is capped at 6 because in a still life a fully live 8-neighbourhood would violate the survival rules — the centre cell would be surrounded by more than 3 live neighbours and could not survive.

### Constraints

1. **Neighbour count**: `s[r, c]` is defined as the sum of `a[rr, cc]` over all eight neighbouring cells (clamped to grid boundaries).

2. **Dead-cell stability**: A dead cell (`a[r,c] = 0`) must _not_ have exactly 3 live neighbours, because that would cause a birth in the next generation, breaking the still-life property.

3. **Live-cell stability**: A live cell (`a[r,c] = 1`) must have exactly 2 or 3 live neighbours, because any other count would cause it to die in the next generation.

4. **Boundary conditions**: Along each edge, no three consecutive cells in the row or column adjacent to the border can all sum to 3 or more live cells. This prevents edge cells from being "born" or "dying" through interactions near the boundary.

### Objective

$$\text{maximise} \sum_{r=1}^{n} \sum_{c=1}^{n} a[r, c]$$

The goal is to **maximise the total number of live cells** while satisfying all stability constraints.

## Notes and Uncertainty

- The model's author notes some uncertainty about tight lower bounds on neighbourhood sizes: edge cells may always require at least 1 live neighbour and interior cells at least 2 in any valid still life, but this has not been formally proven within the model.
- The maximum density achievable grows roughly as $O(n^2)$, but the exact optimal value for large $n$ is non-trivial to compute.
- Instance difficulty scales quickly with $n$; even modest grid sizes can be computationally demanding.

## References

- **Model author**: Ralph Becket `<rafe@csse.unimelb.edu.au>`, University of Melbourne.
- Conway's Game of Life: M. Gardner, "Mathematical Games — The fantastic combinations of John Conway's new solitaire game 'life'", _Scientific American_, 223(4):120–123, 1970.
- The still-life problem has been studied as a constraint satisfaction benchmark; see, e.g., B. Bremermann, and work within the MiniZinc benchmark suite.
