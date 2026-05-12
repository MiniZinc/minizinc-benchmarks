# Blocks World

## Problem Description

The **Blocks World** problem is a classic planning puzzle in artificial intelligence and constraint programming. A set of numbered blocks are arranged in stacks (piles). The goal is to rearrange them from a given **start configuration** into a specified **goal configuration** by moving one block at a time, using as few moves as possible.

The only legal move is to take the **topmost** block from any stack and place it on top of another stack (or start a new stack on the floor). You cannot move a block that has another block resting on top of it.

### Example

```
Start:                   Goal:
  Pile 1: [7, 5, 3, 9]    Pile 1: [6, 9, 1, 3, 4, 5]
  Pile 2: []               Pile 2: [7]
  Pile 3: [8, 4, 6, 1, 2]  Pile 3: [2, 8]
```

_(Piles are listed bottom-to-top)_

## Parameters

| Parameter | Description                              |
| --------- | ---------------------------------------- |
| `n`       | Number of blocks                         |
| `k`       | Number of piles available                |
| `start`   | Start configuration (see encoding below) |
| `end`     | Goal configuration (see encoding below)  |

### Configuration Encoding

Both `start` and `end` are arrays of length `n`. For each block `c`, `start[c]` stores the block that block `c` is **resting on** in that configuration (or `0` if block `c` is sitting directly on the floor). This encodes each stack as a chain of "sits-on" relationships.

For example, if block 5 is on top of block 7, and block 7 is on the floor: `start[5] = 7` and `start[7] = 0`.

## Decision Variables

| Variable      | Description                                                                                                                                                        |
| ------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `state[c, s]` | The block that block `c` is resting on at step `s`. Encodes the full configuration of all stacks at each point in the sequence of moves.                           |
| `move[i, 1]`  | The block that is picked up on move `i` (0 if no move is made).                                                                                                    |
| `move[i, 2]`  | The block that `move[i,1]` was resting on before being moved (i.e., what it was sitting on).                                                                       |
| `done[s]`     | Whether the goal configuration has been fully achieved by step `s`. Once the goal is reached, `done` stays true for all remaining steps.                           |
| `count[c, s]` | The number of blocks resting directly on block `c` at step `s`. Used internally to ensure each block has at most one block on top of it (a valid stack structure). |
| `objective`   | The total number of moves made to reach the goal. This is the value being minimised.                                                                               |

## Constraints

- **Valid stacking:** At each step, every block can have at most one block directly on top of it (enforced via a global cardinality constraint).
- **State transitions:** The only block that changes its "resting-on" value between two consecutive steps is the block being moved.
- **A block can only be moved if it is on top:** The block being moved must have no other block resting on it (i.e., it must be a "free" top block).
- **Start and end states:** The configuration at step 0 matches the start, and the configuration at the final step matches the goal.
- **Completion flag:** `done[s]` is true exactly when the current configuration equals the goal configuration.
- **Symmetry breaking / lower bound:** Blocks that are already correctly placed and "locked in" (their entire supporting chain is also in place) cannot be unnecessarily moved. Additionally, a do-undo prevention constraint stops a block from being moved and then immediately moved back.

## Objective

Minimise the total number of moves required to reach the goal configuration:

```
minimise objective
```

The maximum number of moves considered is bounded by `n × k` (the product of the number of blocks and the number of piles), which serves as a heuristic upper bound.

## Notes

- The model was written by **Mats Carlsson** and has been used in the MiniZinc Challenge.
- The Blocks World problem is a well-known benchmark originating from early AI planning research (e.g., Winograd, 1971; SHRDLU system). It has since been studied extensively as both a planning and combinatorial optimisation problem.
- The locked-block predicate identifies blocks that are already in their correct final position and whose entire supporting chain below them is also correctly placed; these blocks can be safely ignored for further moves.

## References

- Winograd, T. (1971). _Procedures as a Representation for Data in a Computer Program for Understanding Natural Language_. MIT AI Technical Report 235. (Original context for the Blocks World domain.)
- Slaney, J., & Thiébaux, S. (2001). Blocks World revisited. _Artificial Intelligence_, 125(1–2), 119–153.

## Model update summary

Added concise inline comments in `blocks.mzn` to clarify:

- the main state-tracking arrays (`state`, `count`, `done`, `move`, `locked`) and their roles,
- the two predicates `move` and `nomove` that enforce state transitions, and
- how configurations evolve one block-move at a time from start to goal.
