# Pennies on a Chessboard with Distinct Distances

## What problem does this model solve?

This MiniZinc model tries to place as many pennies as possible on an `n × n` chessboard, with one key rule:

- every pair of placed pennies must be at a different distance from each other.

To keep everything as integers, the model uses **squared Euclidean distance** instead of Euclidean distance itself. This does not change which distances are distinct; it only avoids square roots.

In short, the model is solving a geometric optimization puzzle:

- no two pennies share a square,
- no two penny-pairs share the same distance,
- and the number of placed pennies is maximized.

## Main data and decision variables

- `n`: size of the board.
- `N = 1..n`: row/column index set.
- `is_present[i]` (boolean): whether penny `i` is used.
- `x[i]`, `y[i]` (optional coordinates): row/column of penny `i` when present.
- `xy[i]` (optional linearized cell index): single-number board position for penny `i`.
- `pennies`: total number of pennies placed.
- `distances`: list of squared distances between all pairs `(i, j)` with `i < j`; entries are absent if either penny is absent.

The model allows up to `n` candidate pennies and decides how many of them to actually place.

## Core constraints (high level)

1. **Unique board positions**  
   All used pennies must occupy different cells (`all_different(xy)`).

2. **Unique pairwise distances**  
   All computed pair distances must be different (`all_different(distances)`).

3. **Coordinate consistency**  
   `x[i]`, `y[i]`, and `xy[i]` represent the same location.

4. **Presence consistency**  
   A penny is marked present exactly when its coordinates and position exist.

5. **Counting pennies**  
   `pennies = sum(is_present)`.

6. **Symmetry reduction**  
   Pennies are ordered by position so equivalent reorderings are not treated as different solutions.

## Objective

The solve goal is:

- **maximize `pennies`**.

So the model searches for the largest feasible set of pennies that satisfies the distinct-distance rule.

## Output produced by the model

The model prints:

- a 2D board view (true/false grid indicating occupied cells),
- the list of pairwise squared distances,
- `x` coordinates,
- `y` coordinates,
- and the final number of pennies.

## Notes and references

- The model header says it is inspired by this post:  
  <https://blog.computationalcomplexity.org/2023/06/can-you-put-n-pennies-on-n-x-n.html>
- This task is related in spirit to classic distinct-distance questions in combinatorial geometry (for example, Erdős-style distinct-distance problems).
- I am not fully sure of a single canonical academic paper for this exact optimization variant (“maximize pennies on an `n × n` grid with all pairwise distances distinct”). If you need a strict literature citation for this exact formulation, a domain expert should confirm the best primary source.

## Model update summary

Added concise inline comments in pennies.mzn to clarify:

- optional-coordinate and presence decision variable roles,
- distance uniqueness semantics via squared distances,
- objective intent maximizing feasible penny count.
