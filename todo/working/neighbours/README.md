# Neighbours Problem

## Description

This problem is based on the IBM Research "Ponder This" challenge from December 2012. It involves assigning numbers to residents arranged in a rectangular grid, subject to a neighbourhood rule that limits which numbers can be assigned, with the goal of maximising the total sum of assigned numbers.

**Original challenge:** https://www.research.ibm.com/haifa/ponderthis/challenges/December2012.html

## Problem Setting

Imagine an `n × m` grid where each cell is occupied by exactly one resident. Two residents are **neighbours** if their cells share an edge (not just a corner). For example, in a 3×3 grid, the centre resident has four neighbours (above, below, left, right), while a corner resident has only two.

```
+---+---+---+
| A | B | C |
+---+---+---+
| D | E | F |
+---+---+---+
| G | H | J |
+---+---+---+
```

In the grid above, E's neighbours are B, D, F, and H.

## Assignment Rule

Each resident is assigned a natural number between 1 and 5, subject to the following rule:

> If a resident is assigned a number `N > 1`, then at least one of their neighbours must be assigned the number `N − 1`.

This means a resident can only receive a high number if the "chain" leading down to 1 is supported somewhere in their neighbourhood. For example, a resident assigned 4 requires a neighbour with 3, and that neighbour in turn requires a neighbour with 2, and so on back to 1.

## Objective

The goal is to **maximise the total sum** of all numbers assigned across the entire grid.

## Parameters

| Parameter | Description                   |
| --------- | ----------------------------- |
| `n`       | Number of rows in the grid    |
| `m`       | Number of columns in the grid |

## Decision Variables

| Variable    | Domain         | Description                                                       |
| ----------- | -------------- | ----------------------------------------------------------------- |
| `x[i, j]`   | 1..5           | The number assigned to the resident in row `i`, column `j`        |
| `objective` | `n*m`..`5*n*m` | The total sum of all assigned numbers (the value being maximised) |

## Constraints

1. **Neighbourhood rule:** For every resident assigned a value `N > 1`, at least one of their (up to four) grid neighbours must be assigned `N − 1`.
2. **Border restrictions (redundant):** Residents in the four corners of the grid can be assigned at most 3, since they have only two neighbours. Residents on the border edges (but not corners) can be assigned at most 4, since they have at most three neighbours. These are redundant constraints added to help the solver.
3. **Symmetry breaking:** To reduce the number of equivalent solutions the solver must explore, constraints are added that break the grid's geometric symmetries. For square grids, all 8 symmetries of the square (rotations and reflections) are eliminated. For rectangular grids, the 4 applicable symmetries (horizontal flip, vertical flip, and the identity) are eliminated.

## Notes

- The maximum assignable value is capped at 5. This is an inherent limit because a cell can have at most 4 neighbours, so a value of 6 would require a neighbour with 5, which in turn would need a neighbour with 4, 3, 2, and 1 all reachable — but a cell only has at most 4 neighbours, making a value of 6 impossible to satisfy. _(Note: the model simply enforces an upper bound of 5 without explicitly explaining this reasoning in the code; a domain expert may want to verify this bound is tight.)_
- The model was originally submitted by Peter J. Stuckey and subsequently modified by the MiniZinc team.

## Reference

IBM Research, _Ponder This Challenge — December 2012_.
https://www.research.ibm.com/haifa/ponderthis/challenges/December2012.html
