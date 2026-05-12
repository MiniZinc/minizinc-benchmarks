# Peaceable Queens (MiniZinc)

## Overview

The **Peaceable Queens** problem asks: on an \(n \times n\) chessboard, how many queens of two colors (black and white) can be placed so that queens of opposite colors never attack each other?

This model maximizes the number of black queens, with the rule that the number of black and white queens must be equal. So if the objective is \(k\), the board contains \(k\) black queens and \(k\) white queens.

## What the model represents

Each square is assigned one of three states:

- `EMPTY`
- `BLACK`
- `WHITE`

The board is represented by:

- `n`: board dimension
- `x[i,j]`: the state of square `(i,j)`

The objective variable is:

- `objective`: number of black queens on the board

Because of a balancing constraint, this is also the number of white queens.

## Core constraints (high level)

The model enforces four main ideas:

1. **Peace condition on every row and column**  
   A row/column cannot contain a black queen and a white queen in positions that would attack each other along that line.

2. **Peace condition on every diagonal**  
   The same non-attacking rule is applied to both diagonal directions.

3. **Equal team sizes**  
   Number of black queens = number of white queens.

4. **Symmetry reduction**  
   Equivalent boards created by rotation, reflection, or swapping black/white are removed so the solver avoids exploring duplicate solution shapes.

## Objective

The model solves a maximization problem:

- maximize `objective`
- subject to all peace and balance constraints

In plain language: find the largest equal black/white placement where opposite colors do not attack each other.

## Output

Solutions are printed as a board using:

- `B` for black queens
- `W` for white queens
- `.` for empty squares

The output also includes:

- `n`
- computed `objective`
- a known optimal value (when available) from OEIS sequence A250000 for comparison.

## References

- OEIS A250000 (known best/optimal values for this problem family): https://oeis.org/A250000
- Model comments cite insights from Smith et al. (CP 2004).

> Note on citation detail: the MiniZinc file references “Smith et al., CP'2004”, but does not include full bibliographic metadata (full title, authors list, pages, DOI). If you need a precise academic citation, an additional literature lookup is recommended.

## Model update summary

Added concise inline comments in peaceable_queens_mznc2021.mzn to clarify:

- board-state decision variable semantics,
- objective interpretation as balanced peaceful queen count,
- maximization intent under non-attacking color constraints.
