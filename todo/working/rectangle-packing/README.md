# Rectangle Packing (`rect_packing.mzn`)

## What problem is this model solving?

This MiniZinc model encodes a classic **rectangle packing** benchmark.

Given an integer `n`, you must place one square of each size:

- `1x1`, `2x2`, `3x3`, …, `n x n`

inside a larger enclosing rectangle so that:

- squares do **not overlap**,
- every square is fully inside the enclosing rectangle,
- and the rectangle dimensions are consistent with all placements.

The model enforces `Height <= Width` to avoid counting symmetric rotations of the same container.

## Inputs and derived constants

Main input:

- `n`: largest square size (so there are `n` squares total)
- `Consider_Unit_Square` (bool): whether to include the `1x1` square in placement constraints

Important derived values:

- `Squares = 1..n`
- lower/upper bounds for `Width`, `Height`, and `Area`
- `int_slack` from `slack_frac` (used internally to decompose coordinates)

These bounds make the model tighter and reduce impossible regions of the search space.

## Decision variables

For each square size `i`:

- `X[i]`: x-coordinate of the square’s lower-left corner
- `Y[i]`: y-coordinate of the square’s lower-left corner

Container variables:

- `Width`, `Height`
- `Area`

The model also defines helper variables (`X_div`, `X_rem`, `Y_div`, `Y_rem`) for internal decomposition of coordinates.

## Core constraints (beginner view)

1. **Non-overlap**
   - Uses global constraint `diffn(...)` so any two placed squares cannot intersect.

2. **Inside the container**
   - `X[i] + i <= Width`
   - `Y[i] + i <= Height`

3. **Container consistency**
   - `Height <= Width`
   - `Area = Height * Width`

4. **Capacity-style pruning**
   - Uses `cumulative(...)` on x and y projections to prevent impossible overloads.

5. **Symmetry breaking / dominance rules**
   - Additional constraints reduce equivalent or dominated layouts (for example, rules involving the largest square and forbidden edge gaps).

## Objective

There is **no optimization objective** in this file.

The model ends with `solve satisfy;`, meaning it searches for any feasible packing that satisfies all constraints and reported variables (`Area`, `Height`, `Width`, `X`, `Y`).

> Note: because `Area` is constrained but not minimized here, this specific model instance is feasibility-oriented. Some rectangle-packing variants instead use `solve minimize Area;`.

## Uncertainty and interpretation notes

- The comments describe an “optimized variant” (smallest area), but the current solve item is `satisfy`; this may indicate a benchmark variant, a staged solve process, or intentional feasibility testing.
- The fixed `fgaps` table and dominance rules are specialized; without the accompanying paper/code history, their exact derivation cannot be fully reconstructed from this file alone.
- `Consider_Unit_Square = false` pins square `1x1` at `(0,0)` and removes it from most placement constraints; this likely serves performance experiments.

## References identifiable from the model

- MiniZinc global constraints used:
  - `diffn` (non-overlap for rectangles)
  - `cumulative` (resource/capacity over intervals)
- In-model citation:
  - H. Simonis, B. O’Sullivan, _Search Strategies for Rectangle Packing_ (mentioned in comments as inspiration for an adapted empty-strip dominance idea).
