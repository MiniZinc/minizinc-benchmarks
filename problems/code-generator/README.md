# Unison Code Generator

## Problem Description

This model implements **combined instruction selection, register allocation, and instruction scheduling** for a compiler back-end. These three tasks are classic steps in turning a program's intermediate representation into efficient machine code:

- **Instruction selection**: choosing which concrete machine instruction to use for each operation (e.g., a plain add, an add-with-shift, etc.).
- **Register allocation**: assigning each intermediate value (called a _temporary_) to a physical processor register. If not enough registers are available, a temporary may be _spilled_ — written to memory and reloaded later.
- **Instruction scheduling**: deciding the order (clock cycle) in which instructions execute, subject to data dependencies and hardware resource constraints (e.g., functional unit capacities).

Traditional compilers solve these three problems one after another, which can give suboptimal results because the decisions interact strongly. This model solves them **simultaneously**, allowing a better overall solution to be found.

The model is the MiniZinc encoding used by the **Unison** tool, an open-source framework for combinatorial code generation (http://unison-code.github.io), developed at RISE SICS AB.

The program to be compiled is represented as a set of **basic blocks** — straight-line sequences of operations with no internal branches. Each block has a measured execution frequency, so the model can prioritise reducing the runtime of hot code paths.

---

## Input Data

The input describes a single function to be compiled:

| Parameter                           | Meaning                                                                                            |
| ----------------------------------- | -------------------------------------------------------------------------------------------------- |
| `bb_ops`, `bb_operands`, `bb_temps` | Sets of operations, operands, and temporaries belonging to each basic block                        |
| `bb_frequency`                      | Estimated execution frequency of each basic block                                                  |
| `bb_maxcycle`                       | Maximum allowed cycle for the last operation in a block                                            |
| `op_instructions`                   | Set of candidate machine instructions for each operation                                           |
| `op_type`                           | Type of each operation (linear, branch, call, copy, etc.)                                          |
| `op_mand`                           | Whether an operation is mandatory (must execute) or optional (e.g., a copy that may be eliminated) |
| `operand_temps`                     | The candidate temporaries that can supply each operand                                             |
| `operand_use`                       | Whether an operand reads (`true`) or writes (`false`) a value                                      |
| `temp_width`                        | The register width (in register slots) required by each temporary                                  |
| `atom_regs`                         | The set of physical registers belonging to each register atom (class)                              |
| `res_cap`, `res_con`, `res_dur`     | Resource capacities, consumptions, and durations for each functional unit                          |
| `lat_table`                         | Instruction latencies — the minimum number of cycles between a definition and its uses             |
| `calleesaved`, `callersaved`        | Sets of callee-saved and caller-saved registers                                                    |

---

## Decision Variables

| Variable     | Type          | Meaning                                                                                                                                      |
| ------------ | ------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| `a[o]`       | Boolean       | Whether operation `o` is **active** (actually executed). Mandatory operations are always active; optional copy operations may be eliminated. |
| `ii[o]`      | Integer index | Which machine instruction is selected for operation `o` (an index into the operation's candidate instruction list).                          |
| `c[o]`       | Integer       | The **clock cycle** at which operation `o` is issued. A value of `-1` means the operation is inactive.                                       |
| `y[p]`       | Integer index | Which temporary is chosen to supply operand `p` (an index into the operand's candidate temporary list).                                      |
| `r[t]`       | Integer       | The **physical register** assigned to temporary `t`. A value of `-1` means the temporary is not live (inactive).                             |
| `rt[p]`      | Integer       | The physical register seen at operand `p` (derived from `r` and `y`).                                                                        |
| `ls[t]`      | Integer       | The cycle at which temporary `t` becomes **live** (is defined).                                                                              |
| `ld[t]`      | Integer       | The **live duration** of temporary `t` (number of cycles it occupies a register).                                                            |
| `le[t]`      | Integer       | The cycle at which temporary `t` ceases to be live (`ls + ld`).                                                                              |
| `lt[p]`      | Integer       | The **latency** associated with operand `p` for the chosen instruction.                                                                      |
| `s[p]`       | Integer       | A **slack** variable for operand `p`, used to balance latencies when a temporary value flows across block boundaries.                        |
| `copysum[b]` | Integer       | The number of active optional (copy) operations in basic block `b`.                                                                          |
| `objective`  | Integer       | The value being minimised (see below).                                                                                                       |

---

## Objective

The model has two optimisation modes, controlled by the Boolean parameter `optimize_cycles`:

- **`optimize_cycles = true`** (the primary goal): minimise the **weighted execution time**, computed as the sum over all basic blocks of _(block frequency) × (issue cycle of the block's last operation)_. This directly reduces the expected runtime of the compiled function.
- **`optimize_cycles = false`**: minimise total **resource consumption** (a proxy for spill cost / register pressure, used during a preprocessing phase).

---

## Key Constraints

- **Activation**: an operation is active if and only if it is issued at a non-negative cycle; mandatory operations are always active.
- **Instruction selection**: each active operation is assigned exactly one machine instruction from its candidate set, which determines register classes, latencies, and resource usage.
- **Temporary selection**: each operand is connected to exactly one temporary, which must be live at the time the operation executes.
- **Register assignment**: each live temporary is assigned a physical register; temporaries of width > 1 occupy a contiguous block of registers.
- **Disjoint live ranges**: two temporaries that are simultaneously live must not be assigned overlapping registers (the core register allocation constraint, modelled as a `diffn`/non-overlap constraint over time and register space).
- **Data precedences**: if operation B uses a value defined by operation A, then B must be scheduled sufficiently many cycles after A to respect the instruction latency.
- **Resource constraints**: functional units have limited capacity; the `cumulative` constraint ensures no unit is overloaded in any cycle.
- **Preassignments**: some operands are forced to specific registers (e.g., argument and return-value registers dictated by the calling convention).
- **Callee-saved register spilling**: a callee-saved register is spilled (saved/restored around calls) if and only if some temporary's live range conflicts with it.
- **Copy elimination**: an optional copy operation is eliminated (set inactive) when the source and destination temporaries can be assigned the same register.

---

## References

This model is the MiniZinc encoding used by the Unison integrated code generation tool. The underlying combinatorial approach is described in:

> Roberto Castañeda Lozano, Mats Carlsson, Gabriel Hjort Blindell, Christian Schulte.  
> **Combinatorial Register Allocation and Instruction Scheduling.**  
> _ACM Transactions on Programming Languages and Systems (TOPLAS)_, 41(3), Article 18, 2019.  
> https://doi.org/10.1145/3301488

> Roberto Castañeda Lozano, Mats Carlsson, Frej Drejhammar, Christian Schulte.  
> **Constraint-Based Instruction Scheduling for a Commercial Real-Time Operating System.**  
> _Principles and Practice of Constraint Programming (CP)_, 2012.

The Unison project and source code are available at: http://unison-code.github.io
