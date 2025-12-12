# Blocks World Puzzle in MiniZinc

## Overview

This MiniZinc model solves the **Blocks World Puzzle**, a classic problem in artificial intelligence and planning. The puzzle involves transforming an initial configuration of numbered blocks stacked into piles into a specified goal configuration. Blocks can only be moved one at a time, and the aim is to achieve the goal with the **minimum number of moves**.

---

## Problem Description

- **Initial State**: Blocks are arranged in a set of piles.
- **Goal State**: A different arrangement of the same blocks across the piles.
- **Allowed Action**: Move one block from the top of a pile to the top of another pile.
- **Objective**: Minimise the number of moves required to reach the goal configuration.

Example:

- **Start**:
  - Pile 1: [7, 5, 3, 9]
  - Pile 2: []
  - Pile 3: [8, 4, 6, 1, 2]
- **Goal**:
  - Pile 1: [6, 9, 1, 3, 4, 5]
  - Pile 2: [7]
  - Pile 3: [2, 8]

---

## Key Parameters

- `n`: Number of blocks.
- `k`: Number of piles.
- `start[c]`: Initial pile index for block `c`.
- `end[c]`: Goal pile index for block `c`.
- `nk`: Maximum number of steps (heuristic upper bound = n × k).

---

## Decision Variables

- `state[c, s]`: Pile position of block `c` at step `s`.
- `count[p, s]`: Number of blocks in pile `p` at step `s`.
- `done[s]`: Boolean indicating if the goal state is reached at step `s`.
- `move[s, 1..2]`: Represents a move at step `s`:
  - `move[s,1]`: Block being moved.
  - `move[s,2]`: Previous pile of the block.
- `objective`: Total number of moves (to be minimised).

---

## Constraints

1. **Initial and Goal States**:
   - `state[c,0] = start[c]`
   - `state[c,nk] = end[c]`
2. **Move Validity**:
   - Only one block changes position per step.
   - Moves respect pile capacity and block positions.
3. **Global Cardinality**:
   - Tracks the number of blocks per pile at each step.
4. **Symmetry Breaking**:
   - Prevent redundant moves (e.g., undoing previous moves).
   - Limit moves per block to `k`.
   - Avoid unnecessary steps after reaching the goal.
5. **Locked Blocks**:
   - Blocks in their final position should not be moved again.

---

## Objective

Minimise:

$$
\text{objective} = nk + 1 - \sum(\text{done})
$$

This effectively counts the number of steps taken before reaching the goal configuration.

---

## Notes

- The model uses **global constraints** like `global_cardinality_closed` for pile consistency.
- Symmetry-breaking constraints improve efficiency by reducing redundant solutions.
- The heuristic upper bound (`nk`) ensures the search space is finite.

---

### References

- Classic AI planning problem: Blocks World.
