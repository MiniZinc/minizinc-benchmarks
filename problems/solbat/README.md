# Solitaire Battleships — MiniZinc Model Overview

This model encodes **Solitaire Battleships**, a one-player logic puzzle. In this puzzle, you are given a grid together with:

- some **pre-filled hints**,
- the number of ship cells required in each **row** and **column**, and
- the required number of ships of each **length**.

The task is to complete the grid with water and ships so that all puzzle rules are satisfied.

## Problem idea

Battleships puzzles use a fleet made of ships of different lengths:

- length 1: **submarine**
- length 2: **destroyer**
- length 3: **cruiser**
- length 4: **battleship**

Ships may be placed horizontally or vertically. They cannot overlap, and in standard puzzle rules they also cannot touch **diagonally**. The clues tell you how many ship cells appear in each row and column, and some cells may already be marked as water or as parts of ships.

This MiniZinc model is a **satisfaction model**: it does not try to optimize anything. It simply asks the solver to find **any board** that obeys the puzzle rules.

## Main input data

The model expects:

- `width`, `height`: board dimensions
- `maxship`: maximum ship length
- `hint[ROWS, COLS]`: the partially filled puzzle grid
- `rowsum[ROWS]`: number of ship cells in each row
- `colsum[COLS]`: number of ship cells in each column
- `ship[SHIPS]`: how many ships of each length must appear

The board uses symbolic piece types encoded as integers:

- `w`: water
- `c`: submarine (single-cell ship)
- `l`, `r`: left and right ends of a horizontal ship
- `t`, `b`: top and bottom ends of a vertical ship
- `m`: middle segment of a longer ship

## Decision variables

The key decision variable is:

- `board[i,j]`: the content of each cell, chosen from the piece types above

The model also defines:

- `fill[i,j]`: a derived 0/1 view saying whether a cell contains ship material (`1`) or water (`0`)
- `npiece[p]`: how many times each piece type appears in the final solution

An extra border of water is added around the grid. This is a common modelling trick that makes edge and adjacency constraints simpler to write.

## Constraints in plain language

The model enforces the following rules:

1. **Hints are respected.** Any nonzero clue in the input must remain fixed.
2. **The outer border is water.** This avoids special cases at the edges.
3. **`fill` matches `board`.** A cell is filled exactly when it is not water.
4. **Ships do not touch illegally.** In particular, diagonal touching is forbidden, and ship ends must have water on the sides where the ship cannot continue.
5. **Ship shapes are valid.**
   - a left end must continue to the right,
   - a right end must continue to the left,
   - a top must continue downward,
   - a bottom must continue upward,
   - a middle piece must connect in exactly one direction pair (horizontal or vertical).
6. **The fleet composition is correct.** The counts of submarines, ends, and middle pieces must match the requested numbers of ships.
7. **Ships of each length are counted correctly.** The model explicitly counts horizontal and vertical ships of every length from 2 up to `maxship`.
8. **Row and column totals are respected.** The number of occupied cells in each row and column must match the puzzle clues.

## Objective

There is **no objective function**.

The model ends with:

- `solve satisfy;`

So the solver only needs to find a feasible completed board.

## Output

The output prints:

- a human-readable board using symbols such as `.`, `c`, `l`, `r`, `t`, `b`, and `m`, and
- the row and column totals,
- plus a full `board = array2d(...)` representation.

## Notes and uncertainty

A few details are inferred from the model rather than stated in a separate problem description. For example, the exact meaning of each hint value is implied by the piece encoding, and the source comments suggest this is an “improved” version of an earlier model. Also, the comments on `width` and `height` appear swapped, but the indexing still makes the intended board structure clear.

## References

Identifiable references from the source itself:

- The model comments say: **“By Peter Stuckey August 2009”**.
- The puzzle family is explicitly identified as **Solitaire Battleships**.

No more specific publication or external source is identified directly in the file, so any stronger attribution would require checking material outside this directory.

## Model update summary

Added concise inline comments in sb.mzn to clarify:

- board-state and occupancy decision variable semantics,
- fleet-shape and row/column clue feasibility interpretation,
- satisfaction-only solve intent for valid puzzle completion.
