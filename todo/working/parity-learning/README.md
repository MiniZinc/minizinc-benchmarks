# Parity Learning (Minimal Disagreement Parity)

## Overview

This model solves a **parity learning** problem with noisy data.

You are given many input/output examples of an unknown Boolean rule. The hidden rule is assumed to be:

- choose some subset of input variables,
- output the **parity** (even/odd count of `true` values) of that subset.

Because the data may contain mistakes (noise), not every sample must match perfectly. The model therefore finds the parity rule that disagrees with as few samples as possible.

---

## Problem being solved

For each sample:

- you have a vector of Boolean inputs (`sample_inputs`), and
- one Boolean output (`sample_outputs`).

The model chooses which input positions belong to the hidden subset. For each sample, it computes the parity implied by that choice and compares it with the observed output.

The goal is to minimize the number of mismatches (errors), subject to a user-provided upper bound (`max_errors`).

---

## MiniZinc inputs (parameters)

- `num_vars`: number of Boolean input variables per sample.
- `num_samples`: number of samples.
- `max_errors`: maximum number of mismatches allowed.
- `sample_inputs[s, v]`: Boolean value of variable `v` in sample `s`.
- `sample_outputs[s]`: observed Boolean output for sample `s`.

The model also checks basic validity (for example, positive sizes and a nonnegative error bound).

---

## Decision variables

- `parity_bits[v]` (Boolean):
  - `true` means variable `v` is included in the hidden parity subset.
  - `false` means it is not included.

- `computed_parities[s]` (Boolean):
  - parity predicted by the chosen subset for sample `s`.

- `num_errors` (integer):
  - number of samples where predicted parity and observed output differ.

---

## Core constraints

For each sample `s`, the model enforces:

- `computed_parities[s]` equals XOR over all variables of
  - (`parity_bits[v]` AND `sample_inputs[s, v]`).

Intuition: only selected variables contribute to parity, and parity is true when an odd number of contributing values are true.

Then:

- `num_errors` is the count of samples with
  - `sample_outputs[s] != computed_parities[s]`.

---

## Objective

The model solves an optimization problem:

- **minimize `num_errors`**.

So the solver returns the parity subset that best fits the data under the allowed error bound.

---

## Output interpretation

The model prints:

- the selected parity bits as `0/1`,
- total disagreements (`num_errors`) out of `num_samples`,
- and, if any errors exist, the list of disagreeing sample indices.

---

## Notes and references

This model is an optimization variant of the **Minimal Disagreement Parity (MDP)** problem.

References mentioned in the model source:

- James M. Crawford, Michael J. Kearns, and Robert E. Schapire. _The minimal disagreement parity problem as a hard satisfiability problem_. Technical Report, Computational Intelligence Research Lab and AT&T Bell Labs, February 1994.
- SATLIB parity benchmark description: http://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/PARITY/descr.html

Uncertainty note: this README is based on the MiniZinc model comments and code. I have not independently verified the current availability of the SATLIB URL or whether a peer-reviewed publication supersedes the cited technical report.
