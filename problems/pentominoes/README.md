# Pentominoes (Integer/Automaton Formulation)

## What problem is this model solving?

This MiniZinc model encodes a **pentomino-style tiling** problem on a rectangular board.

In plain terms: we want to fill a board with tile IDs so that each tile appears in a valid pattern and row boundaries are respected. The model uses the `regular` global constraint (finite automata over sequences) to describe valid placements.

## High-level idea

The board is flattened into a 1D array called `board`, but it still represents a 2D grid of:

- `height` rows
- `width` columns

Each board cell stores an integer value interpreted as either:

- a tile label (`filled..ntiles`), or
- a special end-of-row marker (`ntiles+1`) in the last column of each row.

So each row is forced to end with a separator value, turning the flattened board into a sequence with explicit row boundaries.

## Main data and decision variables

### Parameters (input data)

- `width`, `height`: board dimensions.
- `ntiles`: number of tile types/states represented in this encoding.
- `filled`: lower bound used for allowed board values.
- `size`: length of the `dfa` table.
- `tiles`: metadata for each tile/automaton slice:
  - `Q`: number of automaton states,
  - `S`: alphabet size,
  - `Fstart..Fend`: accepting states range,
  - `Dstart`: start index into transition data.
- `dfa`: packed transition table storage.

### Decision variable

- `board[1..width*height]` with domain `filled..ntiles+1`.

This is the core unknown the solver chooses.

## Constraints

1. **Non-terminal columns cannot be separator**  
   For every row, columns `1..width-1` must not be `ntiles+1`.

2. **Last column must be separator**  
   For every row, column `width` is forced to `ntiles+1`.

3. **Automaton acceptance per tile description**  
   For each `t in 1..ntiles`, the model reconstructs an automaton from `tiles` and `dfa`, then applies:
   - `regular(board, q, s, d, 1, f)`

   Intuitively, this means the full board sequence must be accepted by each automaton specified by the input data.

## Objective

There is **no optimization objective**. The model is a **satisfaction problem**:

- `solve ... satisfy;`

So any assignment of `board` values meeting all constraints is a valid solution.

## Output

The model prints:

- `board` as a 1D array of length `width*height`.

You can reshape it into `height x width` to view row-by-row structure.

## Notes and uncertainty

- The file name suggests pentominoes, but from this model alone we cannot prove the exact tile geometry (e.g., classic 12 free pentominoes) without inspecting the associated `.dzn`/project data.
- The meaning of `filled` is inferred from bounds; it may represent a first valid tile index or pre-filled labeling convention in the dataset.
- The unusual use of multiple `regular` constraints over the same `board` likely encodes a compact intersection of automata; exact semantics depend on how `tiles`/`dfa` are generated.

## References

- MiniZinc language and standard library docs (including global constraints): https://docs.minizinc.dev/
- `regular` global constraint (automaton constraint) in MiniZinc documentation: https://docs.minizinc.dev/en/stable/lib-globals.html
- Background on pentomino tilings: https://en.wikipedia.org/wiki/Pentomino

## Model update summary

Added concise inline comments in `pentominoes-int.mzn` to clarify:

- the role of the flattened board array and row-sentinel value,
- why the sentinel is restricted to row ends, and
- that each `regular` call applies a tile-specific automaton over the same board sequence.
