# SPECK Optimisation

## What this model is about

This MiniZinc model searches for a good **differential trail** through a small number of rounds of the **SPECK** block cipher. In differential cryptanalysis, we track how input bit differences can propagate through a cipher. The goal is usually to find trails that are as likely as possible, because those trails can reveal structural weaknesses or help evaluate security.

Here, the model represents the two SPECK state words round by round and assigns a cost to each round's modular addition. The solver then looks for a non-zero input difference that minimizes the total cost across all rounds.

## Main inputs

The model takes two key parameters:

- `n`: the word size
- `nr`: the number of rounds to model

The rotation constants are derived from `n`:

- `lr = 2` and `rr = 7` when `n = 16`
- otherwise `lr = 3` and `rr = 8`

These match the usual SPECK round structure for the supported word sizes.

## Decision variables

The core variables are:

- `L[0..nr, 0..n-1]`: the left-word difference bits at each round
- `R[0..nr, 0..n-1]`: the right-word difference bits at each round
- `p[0..nr-1]`: a per-round cost for the modular addition step
- `objective`: the total cost, defined as `sum(p)`

All state bits are Boolean, so the model works at the bit-difference level.

## Constraints in simple terms

The model enforces three main ideas.

### 1. The trail must be non-trivial

The initial difference cannot be all zeros:

- at least one bit in round `0` of `L` or `R` must differ

Without this, the solver could choose the trivial zero trail.

### 2. Each round follows the SPECK update rule

For every round, the model applies the usual SPECK-style operations:

- rotate the left word right
- add it to the right word modulo $2^n$
- use the result as the next left word
- rotate the right word left
- XOR it with the new left word to get the next right word

So the model is not searching over arbitrary bit patterns: it is searching only over patterns that are consistent with the cipher round function.

### 3. Modular addition contributes a cost

The predicate `modular_addition_word(...)` models difference propagation through addition. It introduces internal carry-difference variables and counts positions where the carry behavior is not fully determined. That count becomes `p[i]` for round `i`.

Beginner-friendly interpretation: each round's addition may introduce uncertainty, and `p[i]` measures how expensive that uncertainty is.

## Objective

The model solves a **minimization** problem:

- minimize `objective = sum(p)`

So it prefers differential trails with the smallest total round cost.

A likely cryptanalytic interpretation is that smaller total cost means a more probable differential trail. However, the file does not explicitly state the exact probability convention, so this should be treated as an informed interpretation rather than a guaranteed statement.

## What is not essential to the problem statement

The file includes a specific solver search annotation that branches first on `p`, then on `L`, then on `R`. That is useful for performance, but it is **not part of the mathematical problem itself**, so it can be ignored when first learning what the model means.

## Output and benchmark context

The model marks `L`, `R`, `p`, and `objective` as outputs, so a solution describes the full trail and its total cost. The benchmark metadata classifies this as a real-world minimization problem from the 2023 challenge set.

## Uncertainty and assumptions

A few details are inferred rather than explicitly documented in the model:

- `p[i]` appears to be a differential cost derived from uncertain carry behavior
- lower `objective` appears to correspond to a better or more likely trail
- the model concerns **trail optimisation**, not key recovery or full cryptanalysis on its own

Those interpretations are standard for this kind of model, but the file does not include a full prose specification.

## References

Identifiable references from the file and naming:

- **SPECK** lightweight block cipher family
- **Differential cryptanalysis** of ARX-style ciphers (addition, rotation, XOR)
- Copyright notice in the model: **David Gerault (2023)**

The model itself does not cite a paper directly. If a formal citation is needed, the most likely external reference would be the original SPECK design paper/specification, but that is not named explicitly inside the MiniZinc source.
