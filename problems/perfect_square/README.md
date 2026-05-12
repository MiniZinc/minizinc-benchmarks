# Perfect Square (Squared Square) — MiniZinc Model Overview

## What problem is this model solving?

This model represents a **squared square** problem (also called a **perfect square placement** problem):

- You have one large square of side length `size`.
- You must place `n` smaller squares inside it.
- The side lengths of the smaller squares are given by `squars[1..n]`.
- Squares must stay inside the large square and must not overlap.

The goal in this specific model is to find **any valid arrangement** that satisfies all constraints.

## Inputs (data)

The model expects the following data values:

- `n`: number of small squares.
- `size`: side length of the large square container.
- `squars[1..n]`: side lengths of each small square.

> Note: the identifier is spelled `squars` in the model (likely intended as “squares”). This is just a name and does not affect correctness.

## Decision variables

For each small square `i`:

- `x[i]`: x-coordinate of its lower-left corner (domain `0..size`).
- `y[i]`: y-coordinate of its lower-left corner (domain `0..size`).

So the solver decides where each square is placed.

## Constraints

The model enforces two key requirements:

1. **Inside-boundary constraints**
   - `x[i] <= size - squars[i]`
   - `y[i] <= size - squars[i]`

   These ensure each square fits entirely inside the big square (no part crosses the right or top border).

2. **Non-overlap constraint**
   - `diffn(x, y, squars, squars)`

   This global constraint ensures all placed rectangles (here, squares) are pairwise non-overlapping.

## Objective

There is **no optimization objective** (`minimize`/`maximize`) in this model.

- The solve goal is **satisfaction**: find any placement that satisfies all constraints.

## Output

The model prints:

- the array `x`
- then the array `y`

Together, these arrays define the placement of all squares.

## Interpreting a solution (beginner tip)

If a solution returns:

- `x = [x1, x2, ...]`
- `y = [y1, y2, ...]`

then square `i` has:

- lower-left corner at `(xi, yi)`
- side length `squars[i]`

You can draw all such squares on a `size × size` grid to visualize the packing.

## Uncertainty / assumptions

- The model comments say data were copied from a paper; this README does not verify that every provided dataset exactly matches the publication.
- The term “perfect square” can be used slightly differently across sources (e.g., whether all small square sizes must be distinct). This model itself only enforces the constraints explicitly written above.

## References

- N. Beldiceanu, E. Bourreau, H. Simonis, _A Note on Perfect Square Placement_ (as cited in the model comments).
- MiniZinc global constraint library (`globals.mzn`), including `diffn`.

## Model update summary

Added concise inline comments in perfect_square.mzn to clarify:

- placement decision variable semantics for square coordinates,
- non-overlap intent enforced by diffn,
- satisfaction-only solve intent for feasible packings.
