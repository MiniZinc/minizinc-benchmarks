# Search Stress 2

## Problem Description

**Search Stress 2** is a synthetic benchmark designed to stress-test the _search_ component of constraint solvers rather than propagation. It constructs a chain of deliberately obfuscated "equality" constraints that a solver must reason through, then asserts that the endpoints of the chain are _not_ equal — creating a contradiction. A solver must therefore prove the problem **unsatisfiable** (no solution exists), which requires exhaustively exploring the search space before giving up.

The model was submitted to the **MiniZinc Challenge 2009** as a combinatorial satisfiability benchmark.

## Parameters

| Parameter | Description                                         |
| --------- | --------------------------------------------------- |
| `m`       | Number of rows in the chain (controls chain length) |
| `n`       | Domain size of the integer variables                |

Instance files are named `MM_NN.json` where `MM` = `m` and `NN` = `n`. For example, `04_05.json` sets `m = 4` and `n = 5`. Instance sizes in this benchmark range from tiny (`m=2, n=7`) up to moderate (`m=7, n=2`), allowing solvers to be tested across different difficulty axes.

## Variables

The model declares a single two-dimensional array:

```
array[1..m, 0..n] of var 0..n: t
```

- `t[i, 0]` is the **connector variable** for row `i`. Consecutive connectors `t[i, 0]` and `t[i+1, 0]` are linked by a predicate.
- `t[i, 1..n]` are **auxiliary variables** for row `i`, used internally by whichever equality predicate is applied to that row.

All variables have domain `0..n`.

## Constraints

### Four equality predicates (applied cyclically)

Four predicates — `eq1`, `eq2`, `eq3`, `eq4` — each encode the relationship "x equals y" in a different indirect, roundabout way:

| Predicate | How it (attempts to) encode x = y                                                                                                                                           |
| --------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `eq1`     | Auxiliary variables `z[1..n-1]` are pairwise distinct, nonzero, and different from both `x` and `y`; `z[n] = 0`. This excludes enough values to make propagation difficult. |
| `eq2`     | Both `x` and `y` are constrained to equal the same sum of binary variables `z[i] ∈ {0,1}`, so `x = y = Σz[i]`.                                                              |
| `eq3`     | The auxiliaries form a non-decreasing sequence `x ≤ z[1] ≤ … ≤ z[n] ≤ y`, combined with `x ≥ y`, forcing `x = y`.                                                           |
| `eq4`     | Uses three logically equivalent but redundant rewritings of `x = y` (`x == y`, `x ≥ y ∧ x ≤ y`, `¬(x ≠ y)`), plus forces all auxiliaries to zero.                           |

These are applied in order (cycling through 1→2→3→4→1→…) for each consecutive pair of rows.

### Chain structure

```
eq_k( t[i,0], t[i+1,0], n, [t[i,1], …, t[i,n]] )   for i in 1..m-1
```

Each predicate logically forces `t[i,0] = t[i+1,0]`, so the whole chain would imply `t[1,0] = t[m,0]`.

### Contradiction

```
t[1,0] != t[m,0]
```

This final constraint directly contradicts the equality chain, making every instance **unsatisfiable**. The benchmark measures how quickly different solvers can _prove_ unsatisfiability.

## Objective

There is no optimisation objective — this is a **satisfaction** (`solve satisfy`) problem. Because the model is always unsatisfiable, the goal is to determine that no solution exists as quickly as possible.

## Why Is It Hard?

The four equality predicates are specifically engineered to limit constraint propagation. A propagation-only solver may fail to detect the contradiction early and instead resort to large amounts of search (backtracking). The benchmark therefore isolates and measures the _search efficiency_ of a solver rather than its propagation strength.

## Uncertainty / Caveats

- The model was likely purpose-built for benchmarking and may not correspond to any real-world combinatorial problem.
- The original author is not identified in the model file; the MiniZinc Challenge 2009 proceedings may contain further details.
- Whether all parameter combinations are always UNSAT (or only appear so in the provided instances) is not documented in the model itself.

## References

- MiniZinc Challenge 2009: <https://www.minizinc.org/challenge2009/results2009.html>

## Model update summary

Added concise inline comments in `search_stress2.mzn` to clarify:

- that `eq1`..`eq4` are alternate equality encodings used for stress testing,
- how the row-to-row equality chain is built, and
- that the final endpoint inequality intentionally creates an UNSAT benchmark.
