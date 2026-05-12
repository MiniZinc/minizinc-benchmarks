# Quasigroup 7 (QG7) — MiniZinc Model Guide

## What problem is this model solving?

This model checks whether a **quasigroup of order `n`** exists under an additional algebraic rule called **Axiom 7**.

A quasigroup here is represented as an `n × n` table (like a multiplication table) over values `0..n-1`, where:

- each value appears exactly once in every row, and
- each value appears exactly once in every column.

So the table is a Latin square, plus extra constraints.

The special rule in this model is:

- for all `i, j`: `Q[i, Q[j,i]] = Q[Q[j,i], j]`

This is the model’s form of **Axiom 7**.

## Inputs and outputs

- **Input parameter:** `n` (the order/size of the quasigroup).
- **Output:** a concrete `n × n` table `quasiGroup` if constraints are satisfiable.

The model is a feasibility model (`satisfy`): it looks for any valid table, not the “best” one.

## Decision variables

- `quasiGroup[row, col]` for `row, col in 0..n-1`
- Each cell is an integer variable in `0..n-1`.

Interpretation: `quasiGroup[r,c]` is the table entry at row `r`, column `c`.

## Core constraints (beginner view)

1. **Row uniqueness**
   - Every row has all different values (`all_different`).
2. **Column uniqueness**
   - Every column has all different values.
3. **Fixed diagonal**
   - `quasiGroup[i,i] = i` for all `i`.
   - This normalizes the table and reduces symmetry.
4. **Axiom 7 condition**
   - `quasiGroup[i, quasiGroup[j,i]] = quasiGroup[quasiGroup[j,i], j]` for all `i, j`.
5. **Additional implied/helper inequality**
   - `quasiGroup[i,n-1] + 2 >= i` for all `i`.
   - This appears to be an extra strengthening constraint to prune invalid structures.

## Objective

There is **no optimization objective** in this model.

- It uses `solve satisfy`, meaning the goal is only to find a feasible quasigroup satisfying all constraints.

## Notes on uncertainty / interpretation

- The model comments call one inequality “some implied? constraint”, suggesting uncertainty about whether it is logically implied by other axioms or simply added as a helpful strengthening condition.
- The comments also discuss quasigroup existence/non-existence for several sizes; this README does not independently verify those claims.
- The model uses domain `0..n-1`, while some literature states quasigroups over `1..m`; this is a standard indexing shift.

## References

Identifiable references from the model comments:

- CSPLib Problem 003 (Quasigroup Existence):
  - http://www.dcs.st-and.ac.uk/~ianm/CSPLib/prob/prob003/index.html
  - http://www.dcs.st-and.ac.uk/~ianm/CSPLib/prob/prob003/spec.html
- Model provenance note in file comments:
  - Translation from an ESSENCE'/Minion Translator example (`quasiGroup7.eprime`)
  - Commented author attribution: Hakan Kjellerstrand (`hakank.org/minizinc`)

## Model update summary

Added concise inline comments in quasigroup7.mzn to clarify:

- quasigroup table decision variable semantics,
- axiom-7 and Latin-square feasibility interpretation,
- satisfaction-only solve intent (no optimization objective).
