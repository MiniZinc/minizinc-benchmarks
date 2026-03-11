# Instruction Selection

## Problem Description

Instruction selection is a fundamental phase in compiler code generation. When a
compiler translates a program, it first produces an intermediate representation
(IR) — an abstract description of the computations the program must perform. The
instruction selection phase maps those abstract computations to concrete
instructions provided by the target processor.

Specifically, this model solves **global instruction selection**: given a
program function represented as a graph of _operations_ (computations),
_data_ (values produced and consumed), and _blocks_ (groups of operations that
execute sequentially, similar to paragraphs in a program), the goal is to
choose a set of instructions from the target machine that together implement
every operation in the function, while minimising the total execution cost.

Each candidate instruction is called a **match**: it describes a pattern of
operations and data from the function's IR that a single machine instruction can
implement, along with the latency (execution time) of that instruction. The
solver must pick exactly one match covering each operation and each data value,
place each selected match in an appropriate block, assign each value to a
storage location (register), and order the blocks into a linear sequence for
the final program output.

This model was developed by Gabriel Hjort Blindell at KTH Royal Institute of
Technology and is associated with his research on universal instruction
selection using constraint programming.

## Model Parameters

| Parameter                                                        | Meaning                                                                                                 |
| ---------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| `numOperationsInFunction`                                        | Number of operations (computations) in the program function                                             |
| `numDataInFunction`                                              | Number of data values (operands/results) in the function                                                |
| `numBlocksInFunction`                                            | Number of basic blocks in the function's control-flow graph                                             |
| `entryBlockOfFunction`                                           | The block where execution of the function begins                                                        |
| `domSetOfBlockInFunction`                                        | For each block, the set of blocks that dominate it (i.e., every execution path goes through them first) |
| `defEdgesForBlockInFunction`                                     | Data values whose definitions are fixed to a particular block                                           |
| `statesInFunction`                                               | Data values that represent program state (not stored in ordinary registers)                             |
| `execFrequencyOfBlockInFunction`                                 | How often each block is expected to execute (used to weight the cost)                                   |
| `numLocations`                                                   | Number of physical storage locations (registers) on the target machine                                  |
| `numMatches`                                                     | Total number of candidate instruction matches                                                           |
| `operationsCoveredByMatch`                                       | Which operations each match implements                                                                  |
| `dataDefinedByMatch`                                             | Which data values each match produces                                                                   |
| `dataUsedByMatch`                                                | Which data values each match consumes                                                                   |
| `entryBlockOfMatch`                                              | If a match spans multiple blocks, the block it must be placed in                                        |
| `spannedBlocksInMatch`                                           | The set of blocks that a match may span                                                                 |
| `consumedBlocksInMatch`                                          | Blocks that are "absorbed" by a match and cannot be used independently                                  |
| `codeSizeOfMatch`                                                | Code size (in bytes) of each match (present but not used in the objective here)                         |
| `latencyOfMatch`                                                 | Execution latency of each match                                                                         |
| `applyDefDomUseConstraintForMatch`                               | Whether the dominance constraint should be enforced for each match                                      |
| `nonCopyMatches`                                                 | Matches that are not simple data-copy instructions                                                      |
| `sameLoc`, `inBlock`, `inBlockSucc`, `locDomain`, `funLocDomain` | Encoded side constraints from the target machine description                                            |
| `Dominated`                                                      | Matches that are strictly worse than another match and can be excluded                                  |

## Decision Variables

| Variable   | Meaning                                                                                                                          |
| ---------- | -------------------------------------------------------------------------------------------------------------------------------- |
| `sel[m]`   | Boolean: is match `m` selected (i.e., does this instruction appear in the final program)?                                        |
| `def[e]`   | Which basic block contains the definition (production) of data value `e`                                                         |
| `loc[e]`   | Which register or storage location holds data value `e` (`locValueForNull` means the value is not stored in a register)          |
| `place[m]` | Which basic block match `m` is placed in (`blockValueForNull` means the match is not selected)                                   |
| `succ[b]`  | The block that immediately follows block `b` in the final linear code layout; together these form a total ordering of all blocks |

## Constraints

- **Full coverage**: Every operation in the function must be covered by exactly
  one selected match; every data value must be defined by exactly one selected
  match.
- **Placement**: A selected match must be placed in a valid block (not the null
  block). Matches with a fixed entry block must be placed there.
- **Definition placement**: Data values defined by a match must be located in
  the block where the match is placed, or within the blocks that match spans.
- **Consumed blocks**: No match may be placed in a block that is consumed
  (absorbed) by another selected match.
- **Dominance**: For most matches, a data value must be defined in a block that
  dominates (comes before in all execution paths) every block where the value
  is used.
- **Block ordering**: The `succ` array must form a single circuit visiting every
  block exactly once (enforced by the `circuit` global constraint). This
  encodes a total linear order on blocks. The entry block of the function must
  appear first.
- **Location constraints**: Various constraints from the target machine restrict
  which registers particular values may use, whether two values must share the
  same register, and where particular matches must be placed.
- **Dominated match elimination**: Matches that are provably never better than
  another available match are excluded from selection.

## Objective

Minimise the total **execution-frequency-weighted latency** of all selected
matches:

$$\text{minimise} \sum_{m \in \text{selected}} \text{latency}(m) \times \text{execFrequency}(\text{place}(m))$$

Matches placed in blocks that execute more frequently contribute more to the
cost, so the solver is encouraged to choose lower-latency instructions for
hot code paths.

## References

- Gabriel Hjort Blindell, _Instruction Selection: Principles, Methods, and
  Applications_, Springer, 2016.
  [doi:10.1007/978-3-319-34019-7](https://doi.org/10.1007/978-3-319-34019-7)
- Gabriel Hjort Blindell, "Universal Instruction Selection", PhD Thesis, KTH
  Royal Institute of Technology, 2016.
- Roberto Castañeda Lozano, Mats Carlsson, Gabriel Hjort Blindell, and
  Christian Schulte, "Combinatorial Register Allocation and Instruction
  Scheduling", _ACM Transactions on Programming Languages and Systems_, 41(3), 2019. [doi:10.1145/3301321](https://doi.org/10.1145/3301321)
