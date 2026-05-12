# Fillomino

## Overview

This MiniZinc model solves **Fillomino** puzzles. In Fillomino, a rectangular grid must be divided into connected regions, and every cell in a region contains the same number. That number is also the **size of the region**. For example, a region filled with `3` must contain exactly three orthogonally connected cells. In addition, two different regions of the same size are **not allowed to touch side-to-side**.

Some cells are given as clues in the input puzzle, and the model fills in the remaining cells so that all puzzle rules are satisfied.

## Input

The model expects:

- `rows`, `cols`: the dimensions of the grid.
- `puzzle[r,c]`: the starting puzzle.
  - A value `0` means the cell is empty.
  - A value from `1` to `9` is a given clue that must be respected.

## Decision Variables

The model uses four main variable groups.

- `area[r,c]`: identifies **which region** owns cell `(r,c)`.
- `size[a]`: the number of cells in region `a`.
- `what[r,c]`: the final number written in cell `(r,c)`.
- `when[r,c]`: an auxiliary step number showing **how far a cell is from the starting cell of its region**.

The `when` variable is not part of the puzzle itself. It is a helper used to describe each region as growing outward from a single root cell.

## How the Model Represents Fillomino

The model captures the puzzle rules in a direct way:

1. **Clues are fixed**  
   Any nonzero entry in `puzzle[r,c]` must appear unchanged in the final solution.

2. **Each cell shows its region size**  
   The value in `what[r,c]` is forced to equal the size of the region that contains that cell.

3. **Region sizes are counted correctly**  
   For each possible region identifier `a`, `size[a]` is the number of cells whose `area` is `a`.

4. **Regions are connected**  
   Every cell is either:
   - the **root** of its region, or
   - joined to a neighbouring cell in the same region with the same number.

   This gives every region a connected tree-like structure, which ensures the cells of a region form one orthogonally connected block.

5. **Equal-sized neighbouring regions are forbidden**  
   If two side-adjacent cells belong to different regions, those two regions must have different sizes. This is the core Fillomino rule that prevents two separate `3`-regions, `4`-regions, and so on from touching.

## Objective

This model has **no optimisation objective**. It is a **satisfaction problem**:

- the solver only needs to find **any valid completed Fillomino grid**.

## Output

The model prints three arrays:

- `what`: the completed grid of numbers,
- `when`: the auxiliary distance-from-root labels,
- `area`: the region identifier of each cell.

For a puzzle user, `what` is the main solution. The other two arrays help explain how the solver organized the regions.

## Notes

- The model assumes clue values are in the range `1..9`, so it is aimed at standard small-number Fillomino instances.
- I could confirm the puzzle rules from standard Fillomino sources, but I could not verify the original publication or paper for this **specific MiniZinc encoding** from the model file alone.

## References

- Nikoli, “Fillomino” puzzle rules: <https://www.nikoli.co.jp/en/puzzles/fillomino/>
- Wikipedia, “Fillomino”: <https://en.wikipedia.org/wiki/Fillomino>

## Model update summary

Added concise inline comments in fillomino.mzn to clarify:

- region/size/value variable roles,
- helper-variable intent (`when`) for region growth,
- solve mode as pure satisfaction.
