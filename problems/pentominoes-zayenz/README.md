# Pentominoes (MiniZinc model)

## What problem is this model solving?

This model encodes a **pentomino tiling/placement** task on a square board.

- The board has size `size × size`.
- There are `tiles` tile IDs (numbered `1..tiles`).
- The model assigns one tile ID to every board cell.
- A set of automaton expressions (`expressions`) is used to enforce which board patterns are valid.

In beginner terms: the model fills the board with numbered tile labels, then checks those labels against rule automata so that only legal global placements are accepted.

## Data / parameters

The input data defines:

- `size` (`int`): side length of the square board.
- `tiles` (`int`): number of tile IDs.
- `expressions` (`array[int] of string`): regular-language expressions passed to `regular(...)` constraints.

Derived constants:

- `marker = tiles + 1`: a sentinel value used to separate board rows in a flattened sequence.
- `Tiles = 1..tiles`
- `TilesAndMarker = Tiles ∪ {marker}`

## Decision variables

- `board[1..size, 1..size] of var Tiles`  
  Each cell is a decision variable that stores which tile ID is placed there.

- `board_and_markers[...] of var TilesAndMarker`  
  A flattened view of the board with one `marker` inserted after each row.
  This sequence is what the automaton constraints read.

## Constraints

Main constraint:

- For each string in `expressions`, enforce  
  `regular(board_and_markers, expression)`.

Meaning: every provided automaton expression must accept the flattened board sequence. This is how legal shape-placement structure is imposed.

## Objective

There is **no optimization objective**. The model is a **satisfaction problem** (`solve ... satisfy`): find any board assignment that satisfies all constraints.

## Notes on uncertainty

- The exact geometric meaning of each tile ID (which pentomino shape each number represents) is **not explicit in this file**.
- The full semantics of `expressions` depend on how those expressions are generated externally.
- So, while this file clearly defines the variable structure and constraint mechanism, some domain details are delegated to input/generator artifacts.

## References

Identifiable from model header comments:

- Lagerkvist, M. Z., and Pesant, G., _Modeling Irregular Shape Placement Problems with Regular Constraints_.
- Generator repository: https://github.com/zayenz/minizinc-pentominoes-generator
- Model author: Mikael Zayenz Lagerkvist
- License note in model: MIT license (https://opensource.org/licenses/MIT)
