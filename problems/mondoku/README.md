# Mondoku (Balanced GCC Model)

## What problem this model solves

This MiniZinc model generates a colored grid (a "Mondoku" pattern) with two key structure rules:

1. In every **row**, each color appears in exactly one **contiguous block** (one run).
2. In every **column**, each color also appears in exactly one contiguous block.

So colors can repeat in a row/column, but each color’s cells must stay together in a single segment rather than being split into multiple segments.

The model then optimizes for **balance**: it tries to make color usage as even as possible in every row and column.

---

## Inputs

The model expects three parameters:

- `W`: grid width (number of columns)
- `H`: grid height (number of rows)
- `C`: number of colors

Colors are represented as integers `1..C`.

---

## Main decision variable

- `puzzle[w,h]` (for each cell): the color assigned to cell `(w,h)`.

This is the core grid the solver is building.

---

## Helpful derived variables (how contiguity is enforced)

The model constructs two helper arrays:

- `across[w,h]`: marks where a new color-run starts in each row.
- `down[w,h]`: marks where a new color-run starts in each column.

A cell is marked with its color only when it starts a new run; otherwise it is marked `0`.

Using these helper arrays, the model can count how many runs of each color appear in a row/column.

---

## Core constraints

For every row:

- each color must start exactly one run (so exactly one contiguous block per color in that row).

For every column:

- each color must start exactly one run (so exactly one contiguous block per color in that column).

The model uses `global_cardinality` to enforce these counting conditions cleanly.

It also adds a symmetry-breaking constraint (`value_precede_chain`) so equivalent solutions that only rename colors are avoided.

---

## Objective (what is minimized)

The model defines, for each row and each column:

- `max(color_count) - min(color_count)`

This is the spread between the most-used and least-used color in that row/column.

Then it minimizes the **maximum** of all these spreads:

- `objective = max(diff_across ++ diff_down)`

So the solver tries to produce a grid where no row or column is badly imbalanced.

---

## Notes and interpretation

- This is an optimization version of a Mondoku-style generation model, aimed at producing visually balanced patterns.
- The model comment references an online generative-art post as inspiration.
- I could not confirm a canonical academic paper for this exact formulation from the model metadata/comments alone.

If you know the original publication or formal puzzle source, adding it here would improve traceability.

---

## References

- Model comment source: Reddit post “Irregular ‘Mondoku’ art” (r/generative):  
  https://www.reddit.com/r/generative/comments/1fxp5ng/irregular_mondoku_art/
- MiniZinc global constraints (including `global_cardinality`):  
  https://docs.minizinc.dev/en/stable/lib-globals-counting.html

## Model update summary

Added concise inline comments in mondoku-gcc-model-balance.mzn to clarify:

- group-start helper variable semantics,
- objective interpretation as worst imbalance,
- optimization intent for balanced row/column color usage.
