# p1f-pjs

## Overview

This MiniZinc model looks for a **perfect 1-factorization** of the complete graph \(K_n\).

In simple terms:

- A complete graph has all possible edges between nodes.
- A 1-factor (also called a perfect matching) pairs up all nodes so each node appears in exactly one pair.
- A 1-factorization splits all edges of the graph into several such perfect matchings.
- The factorization is **perfect** if taking any two matchings together forms a single cycle visiting every node exactly once (a Hamiltonian cycle).

This is a classic graph-combinatorics problem and is known to be challenging for larger sizes.

## What the model decides

The main decision structure is:

- `p[row, col]`: for matching `row`, gives the node matched with node `col`.

Here:

- `n` = number of nodes in the graph.
- `m = n - 1` = number of matchings in the factorization.

So the matrix `p` has one row per matching and one column per node.

## Meaning of the constraints

The model enforces:

- **No self-pairing**: a node cannot be matched with itself.
- **Each row is a valid matching**: matching is symmetric and one-to-one (if `i` is matched to `j`, then `j` is matched to `i`).
- **Rows partition the edges**: each edge appears in exactly one matching.
- **Perfectness condition**: every pair of rows must combine into a Hamiltonian cycle.
- **Symmetry breaking**: rows are ordered lexicographically to avoid equivalent duplicate solutions.

## Objective

The model includes an optimization objective:

- `objective = sum(i in 1..n)(i * p[1,i])`
- It **minimizes** this value.

This does not change which structures are valid perfect 1-factorizations; it imposes a consistent ordering so one canonical solution is preferred.

## Inputs and outputs

### Required input

- `n`: number of graph nodes.

### Output

- `p`: the full matching matrix.
- `objective`: the minimized ordering value.

## Notes for readers

- The model uses standard global constraints such as `all_different`, `inverse`, `lex_less`, and `circuit`.
- The file header mentions historical compatibility notes (older MiniZinc toolchain behavior), which are implementation details rather than part of the mathematical problem.

## Possible literature context

This model appears to target the well-known **Perfect 1-Factorization** problem in graph theory, often discussed for complete graphs and related conjectures.

Likely relevant background references:

- J. H. Dinitz and D. R. Stinson (eds.), _Contemporary Design Theory: A Collection of Surveys_ (sections on 1-factorizations and perfect 1-factorizations).
- C. C. Lindner and C. A. Rodger, _Design Theory_ (coverage of factorizations and related constructions).
- Surveys and papers on the **Perfect 1-Factorization Conjecture** (especially for complete graphs of even order).

Uncertainty note: the exact paper source for this specific MiniZinc encoding is not explicitly cited in the model file; the author attribution in the header is to Mikael Zayenz Lagerkvist (2009). If you need a precise bibliographic citation for this exact encoding, an additional repository history or publication lookup would be needed.

## Model update summary

Added concise inline comments in p1f-pjs.mzn to clarify:

- matching matrix decision variable semantics,
- objective role as canonical ordering tie-break,
- optimization intent preserving perfect-factorization constraints.
