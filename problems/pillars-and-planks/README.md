# Pillars and Planks (MiniZinc model explainer)

## What problem is this model solving?

This model arranges a set of **planks** (horizontal bars with height 1) and **pillars** (vertical rectangles) inside a fixed 2D area.

- The total space has a fixed width (`available_width`) and height (`available_height`).
- Each plank has a given length (`plank_width`).
- Each pillar has a given width and height (`pillar_width`, `pillar_height`).

The arrangement must satisfy structural rules:

1. Every plank must be supported at **both ends** by pillars.
2. Every pillar must stand on **exactly one support surface**: either the ground (special support index `0`) or one plank.
3. Objects cannot overlap in space.
4. All objects must stay within the available bounding box.

Intuitively, this is a stacking/placement puzzle with stability-style constraints.

## Decision variables (what the solver chooses)

The model chooses positions for all planks and pillars:

- `xk[p], yk[p]`: left endpoint position of plank `p`.
- `xr[r], yr[r]`: bottom-left position of pillar `r`.

It also chooses support relationships:

- `left[p], right[p]`: which pillar supports the left and right end of plank `p`.
- `support[r]`: which plank (or `0` = ground) supports pillar `r`.

A derived variable defines total used height:

- `objective`: maximum top height reached by any plank or pillar.

## Main constraints (beginner view)

- **Inside bounds**  
  Planks and pillars must fit within horizontal/vertical limits.

- **No overlap**  
  `diffn` is used so planks (as 1-unit-high rectangles) and pillars (full-height rectangles) do not overlap.

- **Plank support at both ends**  
  The left endpoint and right endpoint of each plank must lie horizontally within its chosen supporting pillars, and the plank’s `y` must match the top of those pillars.

- **Pillar support**  
  Each pillar must lie entirely on top of its selected support plank (or on ground for `support = 0`), with exact vertical contact (`yr = support_top + 1` where ground is modeled at `-1`).

- **Symmetry breaking**  
  For planks/pillars with identical sizes, ordering constraints reduce equivalent mirrored/permuted solutions.

## Objective

The model **minimizes `objective`**, i.e., it tries to build the structure as low as possible (minimum overall height used).

## Output interpretation

The model prints:

- an ASCII map of the occupied area,
- the final objective value,
- coordinates (`xk`, `yk`, `xr`, `yr`).

The map symbols represent plank ends/body and pillar edges/interior.

## Notes and uncertainty

- The structural rules are clear from the constraints, but the real-world story (e.g., whether this is inspired by a specific puzzle/game or an engineering benchmark) is **not explicitly stated** in the model file.
- Ground support is encoded using index `0` and `y = -1`, which is a modeling trick; beginners may initially find that non-obvious.

## Identifiable references

- MiniZinc global constraint library: `diffn` (included via `include "diffn.mzn"`).
- This explanation is based on the model source file: `pillars-planks-solution.mzn`.

## Model update summary

Added concise inline comments in `pillars-planks-solution.mzn` to clarify:

- plank and pillar position arrays and their meaning,
- the extended arrays that encode ground as index 0 with special height,
- the no-overlap diffn constraint and support relationships, and
- how pillar-support constraints link vertical alignment between objects.
