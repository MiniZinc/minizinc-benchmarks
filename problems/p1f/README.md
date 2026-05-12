# Perfect 1-Factorization of a Complete Graph (`p1f`)

## What problem is this model solving?

This MiniZinc model searches for a **perfect 1-factorization** of the complete graph $K_n$.

- A **1-factor** is a perfect matching: every node is paired with exactly one other node.
- A **1-factorization** splits all edges of $K_n$ into several perfect matchings.
- The factorization is **perfect** if, for every pair of matchings, combining their edges creates a single Hamiltonian cycle (a cycle that visits every node exactly once).

So, the model is trying to arrange pairings of nodes so that:

1. each row is a valid matching,
2. all rows together partition all needed pairings, and
3. any two rows together form one full cycle through all nodes.

---

## Model inputs

- `n`: number of nodes in the complete graph.
- `m = n - 1`: number of matchings (factors) used in the factorization.

---

## Decision variables

The main decision variable is:

- `p[row, col]` (with `row in 1..m`, `col in 1..n`):
  - Interpreted as: in matching `row`, node `col` is matched to node `p[row, col]`.

This means each row of `p` describes one full matching across all nodes.

---

## Constraint meaning (high level)

The model enforces:

- **No self-pairing**: a node cannot be matched with itself.
- **Each row is a matching**: matching is symmetric and valid (if $a$ is paired with $b$, then $b$ is paired with $a$).
- **Rows form a partition of pairings**: the same pairing choice pattern is not reused across factors in a way that breaks factorization.
- **Perfectness condition**: for every two rows, their union must be a Hamiltonian circuit.
- **Symmetry breaking**: rows are ordered lexicographically to avoid exploring equivalent reordered solutions.

---

## Objective

The model includes an optimization objective:

- `objective = sum(i in 1..n)(i * p[1, i])`
- It **minimizes** this value.

This objective does not change the mathematical definition of perfect 1-factorization; it is mainly used to enforce a consistent ordering/selection among equivalent valid solutions.

---

## Output

The model outputs:

- `p`: the full array of matchings.
- `objective`: the minimized ordering value.

---

## Notes on background and references

This model header credits **Mikael Zayenz Lagerkvist (2009)** and appears to be a constraint-programming benchmark formulation for the perfect 1-factorization problem.

Likely relevant mathematical background includes:

- Work on the **Perfect 1-Factorization (P1F) problem/conjecture** in graph theory.
- Literature on 1-factorizations and Hamiltonian decompositions of complete graphs.

I cannot confirm the exact paper this specific MiniZinc encoding was first published in from the model file alone. If you need an exact citation, a good next step is to trace this model via MiniZinc Challenge benchmark archives or Gecode/MiniZinc example repositories authored by Lagerkvist.

## Model update summary

Added concise inline comments in p1f.mzn to clarify:

- matching matrix decision variable semantics,
- objective role as canonical ordering tie-break,
- optimization intent preserving perfect-factorization constraints.
