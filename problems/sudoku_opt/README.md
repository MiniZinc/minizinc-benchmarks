# Sudoku (Optimisation Variant)

## Problem Description

Sudoku is a classic combinatorial puzzle played on an $n \times n$ grid (most commonly $9 \times 9$).
The grid is divided into $\sqrt{n} \times \sqrt{n}$ non-overlapping sub-regions (boxes).
Some cells are given a fixed digit; the task is to fill in the remaining cells so that:

- every **row** contains each digit from $1$ to $n$ exactly once,
- every **column** contains each digit from $1$ to $n$ exactly once,
- every **box** contains each digit from $1$ to $n$ exactly once.

This version is an **optimisation variant**: rather than simply finding any valid completion, the model minimises an objective function derived from the filled-in grid, which can break ties between multiple valid solutions and yield a single canonical answer.

## Parameters

| Name    | Type                           | Meaning                                                                    |
| ------- | ------------------------------ | -------------------------------------------------------------------------- |
| `n`     | `int`                          | Grid dimension (number of rows, columns, and distinct digits; usually 9)   |
| `board` | `array[1..n, 1..n] of opt int` | Partially filled puzzle — cells with no given value are left absent (`<>`) |

`reg = ceil(sqrt(n))` is derived automatically and gives the side-length of each box.

## Decision Variables

| Name        | Domain          | Meaning                                                |
| ----------- | --------------- | ------------------------------------------------------ |
| `x[i, j]`   | `1..n`          | The digit placed in row `i`, column `j`                |
| `objective` | `-(n*n)..(n*n)` | The scalar value being minimised (see Objective below) |

## Constraints

1. **Clue propagation** — For every cell where the puzzle supplies a digit, the model uses the optional-equality operator (`~=`) to require `x[i,j]` to match the given value, while silently ignoring absent cells.

2. **Row uniqueness** — `alldifferent` over each row ensures no repeated digit.

3. **Column uniqueness** — `alldifferent` over each column ensures no repeated digit.

4. **Box uniqueness** — `alldifferent` over each $\text{reg} \times \text{reg}$ sub-region ensures no repeated digit.

## Objective

The model **minimises** a checkerboard-weighted sum of all cell values:

$$\text{objective} = \sum_{i=1}^{n} \sum_{j=1}^{n} x_{i,j} \cdot (-1)^{i+j}$$

Cells on "white" squares of the checkerboard (where $i+j$ is even) contribute positively; cells on "black" squares contribute negatively. This objective is somewhat arbitrary in the sense that it was chosen to make the problem a meaningful optimisation task rather than a pure feasibility puzzle — standard Sudoku puzzles often have a unique solution already, so the optimisation layer is mainly structural.

## Notes and Uncertainties

- The **grid size `n`** is a parameter, so the model generalises beyond the usual $9 \times 9$ case, but the 91 bundled data instances are all $9 \times 9$.
- The **objective function** (checkerboard sum) appears to have been chosen by the original author primarily to demonstrate optimisation search behaviour rather than to model a real-world goal. Its exact motivation is not documented in detail.
- The `~=` operator is MiniZinc's _optional equality_ and quietly passes when a board cell is absent (`<>`), making it safe to use with sparse hint arrays.

## References

- Hakan Kjellerstrand, _Sudoku in MiniZinc_: <http://www.hakank.org/minizinc/>
- Original 91 puzzle instances (Gecode): <http://www.gecode.org/gecode-doc-latest/sudoku_8cpp-source.html>
- Data files: <http://www.hakank.org/minizinc/sudoku_problems2/>
- MiniZinc Challenge Organisers (added search annotation and renamed objective variable)

## Model update summary

Added concise inline comments in sudoku_opt.mzn to clarify:

- grid/clue semantics for the optional board input,
- row, column, and box feasibility constraints,
- optimization intent for the checkerboard-weighted objective.
