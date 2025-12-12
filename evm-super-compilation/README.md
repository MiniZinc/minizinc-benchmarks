# EVM Super Compilation Model

## Overview

This MiniZinc model represents a **super-compilation problem for Ethereum Virtual Machine (EVM)** bytecode. The goal is to transform an initial stack configuration into a desired final stack configuration using a sequence of valid EVM operations, while minimising the number of steps (or optionally other metrics such as gas cost or byte size).

This problem is relevant for **smart contract optimisation**, where reducing the number of instructions or gas usage can significantly improve efficiency and cost-effectiveness.

---

## Problem Description

- **Input**:
  - Initial stack state (`startstack`).
  - Target stack state (`endstack`).
  - A set of allowed EVM operations (e.g., `POP`, `NOP`, `DUP`, `SWAP`, `PUSH`, `ZEROARY`, `UNARY`, `BINARY`, `STOR`).
  - Maximum stack size (`n`) and maximum number of steps (`s`).
- **Goal**: Find a sequence of operations that transforms the initial stack into the final stack while respecting EVM semantics and constraints.

---

## Key Concepts

- **Stack**: A sequence of terms representing data values. Operations manipulate this stack.
- **Operations**:
  - `POP`: Removes the top element.
  - `NOP`: Does nothing.
  - `DUP`: Duplicates an element from a given position.
  - `SWAP`: Swaps the top element with another position.
  - `PUSH`: Pushes a constant value.
  - `ZEROARY`, `UNARY`, `BINARY`: Perform operations with zero, one, or two arguments.
  - `STOR`: Stores values in memory (removes two elements from the stack).
- Each operation has associated **gas cost**, **byte size**, and **input/output terms**.

---

## Decision Variables

- `stack[step, position]`: The term at each stack position for every step.
- `op[step]`: The operation performed at each step.
- `first[opcode]`: The first occurrence of each operation (used for precedence constraints).
- `length`: The number of operations in the sequence.

---

## Constraints

1. **Stack Transformation**:
   - The initial stack matches `startstack`.
   - The final stack matches `endstack`.
   - Each step updates the stack according to the chosen operation.
2. **Operation Validity**:
   - Only real (non-dummy) operations are allowed.
   - Certain operations must appear exactly once (e.g., non-dummy UNARY/BINARY/STOR).
   - Others must appear at least once (e.g., ZEROARY, PUSH).
3. **Precedence Rules**:
   - Enforce ordering for memory-related operations and argument dependencies.
4. **Bounds**:
   - Lower and upper bounds on occurrences of each opcode.
   - Maximum stack size and step count.
5. **Dominance and Redundancy**:
   - Constraints to reduce search space by eliminating equivalent or suboptimal sequences.

---

## Objective

Minimise:

$$
\text{length}
$$

(the number of operations), or alternatively:

- **Gas cost** (`totalgas`).
- **Byte size** (`totalsize`).

---

## Applications

- **Smart Contract Optimisation**: Reduce gas fees and execution time.
- **Formal Verification**: Ensure correctness of transformations.
- **Compiler Design**: Generate efficient EVM bytecode sequences.

---

### References

- Related to optimisation techniques in Ethereum smart contract compilation.
