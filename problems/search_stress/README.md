# Search Stress Test (Graph Colouring)

## Problem Description

This model is a deliberately **unsatisfiable** graph-colouring puzzle designed to stress-test the search and propagation engines of constraint solvers.
The goal is not to find a solution — there is none — but to measure how hard a solver has to work before it can _prove_ that no solution exists.
Benchmarks of this kind are useful for comparing solver efficiency on deep, exhaustive searches.

### Graph Structure

The graph is built by chaining `n` identical subgraphs together in a ring:

```
      x[2]         x[k+2]                         x[(n-1)k+2]
     /    \       /      \                        /           \
x[1]- .. -x[k+1]- ... -x[2k+1]  ...  x[(n-1)k+1]-   ...    -x[nk+1] - x[1]
     \    /       \      /                        \           /
      x[k]         x[2k]                           x[nk]
```

Each subgraph `i` consists of:

- Two **hub** nodes: the left hub `x[(i-1)k+1]` and the right hub `x[ik+1]`.
- `k-1` **spoke** nodes: `x[(i-1)k+2]` through `x[ik]`.

The right hub of one subgraph becomes the left hub of the next, so hubs are shared between neighbouring subgraphs.

## Variables

| Name          | Domain | Meaning                                       |
| ------------- | ------ | --------------------------------------------- |
| `x[1..n*k+1]` | `1..k` | The colour assigned to each node in the graph |

There are `n*k + 1` nodes in total and `k` available colours.

## Constraints

For every subgraph `i` (from `1` to `n`):

1. **Left-hub vs spokes** — the left hub `x[(i-1)k+1]` must differ from every spoke node.
2. **Right-hub vs spokes** — the right hub `x[ik+1]` must also differ from every spoke node.
3. **Spokes all-different** — all `k-1` spoke nodes within the subgraph must have pairwise distinct colours.
4. **Ring closure** — `x[1] != x[n*k+1]` (the first and last hub must differ).

## Why It Is Unsatisfiable

The structure is carefully engineered so that propagation alone forces every hub to take the _same_ colour:

- Within each subgraph, the `k-1` spoke nodes must all be different from each other, consuming `k-1` of the `k` available colours.
- Both the left hub and the right hub must each avoid all `k-1` spoke colours, leaving only one colour for them — they are therefore **forced to be equal**.
- By induction, every hub in the chain `x[1], x[k+1], x[2k+1], \ldots, x[nk+1]` is forced to the same colour.
- The constraint `x[1] != x[n*k+1]` then becomes `colour != colour`, which is a contradiction.

Despite this structural argument, a solver using systematic search cannot shortcut the proof without strong reasoning; it must explore a large portion of the search tree before concluding UNSAT.
Larger values of `n` and `k` make the tree exponentially bigger, stressing the solver further.

## Parameters

| Parameter | Meaning                                            |
| --------- | -------------------------------------------------- |
| `n`       | Number of subgraphs chained together               |
| `k`       | Size of each subgraph (also the number of colours) |

The commented-out example at the bottom of the model (`n = 4; k = 4;`) is a small instance.
Increasing either parameter rapidly increases the difficulty of proving unsatisfiability.

## Objective

There is no objective function — this is a **satisfaction** problem (specifically, an unsatisfiable one).
The measure of interest is solver run-time and the number of search nodes explored before the solver returns `UNSAT`.

## Notes and Uncertainty

- The model is described in its own header as a _"search stress test for propagation engines"_, suggesting it originates in the constraint-programming benchmarking community, but no specific publication or author is credited in the file.
- The choice of search annotation (`first_fail`, `indomain_min`) influences the order in which nodes are explored but does not affect the final UNSAT result.
- Whether a solver can detect the infeasibility through pure propagation (without branching) depends on the strength of its global reasoning; most general-purpose solvers will require significant backtracking.

## Model update summary

Added concise inline comments in search_stress.mzn to clarify:

- graph-coloring decision variable semantics for stress construction,
- unsatisfiable ring-closing contradiction interpretation,
- satisfaction-only solve intent for infeasibility proof.
