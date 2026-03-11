# Radiation (MiniZinc model) — Beginner-friendly overview

## What problem is this model solving?

This model describes a **radiation treatment planning decomposition** problem on a 2D grid.

- You are given a matrix `Intensity[i,j]` (target dose/intensity) for each cell `(i,j)`.
- The model tries to represent that target matrix as a combination of deliverable "shape matrices" (segments).
- Each segment has a beam-on time `b` and covers selected cells.

In plain terms: we want to deliver the requested intensity map while using a plan that is efficient in total beam time and number of segments.

## Inputs (parameters)

- `m`, `n`: number of rows and columns.
- `Intensity[Rows, Columns]`: required intensity at each cell.
- Derived constants:
  - `Bt_max`: maximum intensity value in the grid.
  - `BTimes = 1..Bt_max`: possible beam-on times per segment.
  - `Ints_sum`: sum of all intensities (used as a safe upper bound).

## Decision variables

- `Beamtime`: total beam-on time across all segments.
- `K`: total number of segments (shape matrices).
- `N[b]`: how many segments use beam-on time `b`.
- `Q[i,j,b]`: for cell `(i,j)` and time `b`, how many `b`-segments expose that cell.

Interpretation:

- `Q` explains how each cell receives dose contributions.
- `N` and `K` summarize how many segments are used.
- `Beamtime` summarizes total treatment-on time.

## Main constraints (idea)

1. **Beam time accounting**  
   `Beamtime = sum_b b * N[b]`
2. **Segment counting**  
   `K = sum_b N[b]`
3. **Dose reconstruction per cell**  
   For each cell `(i,j)`:  
   `Intensity[i,j] = sum_b b * Q[i,j,b]`
4. **Row-wise shape bound** (`upper_bound_on_increments`)  
   For each row and each `b`, the model limits how many segments are needed based on increases along columns. This encodes a deliverability-style bound for contiguous/aperture-like shapes.

## Objective

The model minimizes

`objective = (m*n + 1) * Beamtime + K`

This is equivalent to **lexicographic minimization** of:

1. `Beamtime` first,
2. then `K` as a tie-breaker.

Reason: reducing `Beamtime` by 1 always improves objective more than any possible increase in `K`.

## What to remember as a beginner

- The model is a **decomposition model**: exact intensity matching + efficient plan structure.
- `Q` is the detailed explanation of dose delivery; `N`, `K`, `Beamtime` are aggregate quality measures.
- Objective prioritizes shorter treatment time, then fewer segments.

## Uncertainty / assumptions

- The file itself does not include a full clinical machine model, only a mathematical abstraction of segment deliverability via increment bounds.
- Terms like "shape matrix" are inferred from variable names/comments in the model.
- If you need clinical interpretation (e.g., MLC hardware specifics), additional source documentation would be required.

## Identifiable references / provenance

- Header comment: "Radiation problem, MiniZinc 2.0.4 version".
- `metadata.json` indicates this benchmark appears in MiniZinc Challenge instance sets (years listed: 2008, 2012, 2013, 2015, 2020).
- No explicit paper citation is embedded in `radiation.mzn` or `metadata.json`.
