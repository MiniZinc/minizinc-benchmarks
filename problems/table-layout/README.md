# Table Layout (MiniZinc) — Beginner-Friendly Explanation

## What problem is this model solving?
This model chooses a layout for a table so that the **total table height** is as small as possible, while respecting a fixed available page/container width (`pixelwidth`).

Think of each table cell as having several possible renderings (called *configurations*), where each rendering has a known width and height in pixels. The solver picks one configuration per cell, then derives row heights and column widths that can contain all chosen cells.

In short: **pick one shape for each cell so the table fits in width and is as short as possible**.

## Inputs (data)
- `pixelwidth`: maximum available width for the whole table.
- `rows`, `cols`: table dimensions.
- `maxconfig`: maximum number of configurations stored per cell.
- `width[r,c,l]`, `height[r,c,l]`: size of cell `(r,c)` if configuration `l` is chosen.
  - The comment says arrays may be padded with `0` when a cell has fewer real configurations.

The model also computes helper bounds such as global min/max cell width/height and `maxheight` (an upper bound on total height).

## Decision variables
- `config[r,c]`: which configuration index is selected for cell `(r,c)`.
- `cellwidth[r,c]`, `cellheight[r,c]`: the chosen width/height of each cell (linked to `config`).
- `rowheight[r]`: height assigned to each row.
- `colwidth[c]`: width assigned to each column.
- `totalheight`: sum of all row heights.

## Core constraints (plain language)
1. **Table width limit**  
   Sum of all column widths must not exceed available width:
   - `sum(colwidth) <= pixelwidth`

2. **Rows/columns must contain their cells**  
   For every cell `(r,c)`:
   - row `r` must be at least that cell’s height,
   - column `c` must be at least that cell’s width.

3. **Cell size must match chosen configuration**  
   For every cell `(r,c)`, chosen `config[r,c]` determines:
   - `cellwidth[r,c] = width[r,c,config[r,c]]`
   - `cellheight[r,c] = height[r,c,config[r,c]]`

A potential area-based lower-bound constraint is present but commented out.

## Objective
The model minimizes:
- `totalheight = sum(rowheight[r])`

So the solver searches for the shortest possible table (in pixels) that still fits the width bound.

## What the output means
The output prints, for each cell, a pair:
- `(cellheight, cellwidth)`

Then it prints:
- `objective = totalheight`

This gives both the selected per-cell dimensions and the final minimized total table height.

## Uncertainty / caveats
- The comments say invalid padded configurations are marked with `0`, but some helper bounds filter with `>= 0` (which still includes zero). Whether `0` is truly invalid or a valid size is data-dependent.
- If padding uses `0`, the model may still allow selecting those entries unless data or bounds prevent it.
- The intended meaning of `mincellarea` is clear (a per-cell lower-bound idea), but that related constraint is currently disabled.

## References
- Model source: `TableLayout.mzn` in this folder.
- Language reference (general MiniZinc concepts): https://docs.minizinc.dev/
- MiniZinc global/standard library overview: https://docs.minizinc.dev/en/stable/lib.html
