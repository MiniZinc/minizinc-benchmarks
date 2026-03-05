# Instruction Selection (IS)

The `model.mzn` in this directory encodes a classical resource allocation problem that arises
when a compiler chooses machine instructions to implement a high‑level function.  It is
parameterised by a set of operations, data values, basic blocks and possible instruction
`matches` that cover those operations.

## High-level description

- **Operations and Data**: `numOperationsInFunction`, `numDataInFunction`
  describe the size of the function being compiled.
- **Blocks**: Control‑flow blocks are numbered `0..numBlocksInFunction-1`; `entryBlockOfFunction`
  marks the entry block.  `domSetOfBlockInFunction` and related sets describe dominance relations
  and data flow between blocks.
- **Target machine**: `numLocations` indicates the number of registers/locations available.
- **Matches**: Each potential instruction pattern is a "match".  For each match we know
  which operations it covers (`operationsCoveredByMatch`), which data values it defines
  or uses (`dataDefinedByMatch`, `dataUsedByMatch`), the blocks it spans, and its cost in
  `codeSizeOfMatch` and `latencyOfMatch`.  Boolean flags control additional constraints.

Various auxiliary arrays (`sameLoc`, `inBlockSucc`, etc.) encode additional restrictions such as
where data may be placed or whether two elements must share a location.

## Decision variables

- `def[d]` and `loc[d]` assign each data value a defining block and a register location.
- `sel[m]` selects whether a particular match is used.
- `place[m]` places each selected match into a basic block (or the null block).
- `succ[b]` orders the blocks in the generated code.
- `objective` minimises total latency weighted by execution frequency.

## Constraints and objective

The constraints ensure:

1. Every operation in the function is covered by exactly one selected match.
2. Every datum is defined by exactly one selected match (this also forces patterns for inputs
   and constants).
3. Global constraints such as `circuit.mzn` force a valid successor relation on `succ`.

The model maximises code quality by minimising latency (subject to execution frequencies) while
respecting resource and data‑flow constraints.
