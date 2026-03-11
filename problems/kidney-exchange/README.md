# Kidney Exchange (Cardinality-Constrained Multi-Cycle Problem)

## Problem Description

This model solves the **Cardinality-Constrained Multi-Cycle Problem (CCMCP)**, which arises in the context of **kidney exchange programmes**.

In a kidney exchange, patients who need a kidney transplant each have a paired donor (typically a friend or family member) who is willing to donate but is incompatible with their own patient. If patient A's donor matches patient B and patient B's donor matches patient A, a swap can be arranged — this is called an **exchange cycle**. Longer cycles involving three or more patient-donor pairs are also possible.

The goal is to select a set of such exchange cycles across the pool of patient-donor pairs so that the **total benefit (weight) is maximised**, subject to the constraint that no single cycle involves more than **K** pairs. This bound on cycle length exists for practical reasons: all transplants in a cycle must be carried out simultaneously, so longer cycles become logistically difficult.

The CCMCP is NP-hard in general (when $2 < K < \infty$), but solvable in polynomial time when $K = 2$ or $K = \infty$.

## Problem Data

| Parameter          | Description                                                                                                                                                                                                         |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `V`                | Number of vertices (patient-donor pairs) in the compatibility graph                                                                                                                                                 |
| `K`                | Maximum number of pairs allowed in a single exchange cycle                                                                                                                                                          |
| `edge_weight[i,j]` | The benefit (weight) of directing an exchange from pair $i$ to pair $j$; a value of zero for `edge_weight[i,i]` encodes that self-loops are not meaningful; negative values mark infeasible (incompatible) pairings |

## Decision Variables

| Variable    | Description                                                                                                                                |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| `succ[i]`   | The **successor** of vertex $i$ in its assigned cycle — i.e., the next patient-donor pair that will receive a kidney from pair $i$'s donor |
| `cycle[i]`  | An integer **label** identifying which cycle vertex $i$ belongs to; all vertices in the same cycle share the same label                    |
| `objective` | The total weight of all selected edges across all cycles                                                                                   |

## Constraints

1. **Each donor donates to exactly one recipient** (`alldifferent(succ)`): The successor assignments form a permutation, meaning every vertex has a unique successor. This ensures each donor is used at most once.

2. **Cycles are connected** (`cycle[i] == cycle[succ[i]]`): Consecutive vertices along the successor chain must belong to the same cycle, ensuring the assignments form valid closed loops.

3. **Infeasible edges are blocked**: Any edge with a negative weight (representing an incompatible donor-patient pair) is forbidden from appearing in the solution.

4. **Maximum cycle length** (`bin_packing(K, cycle, ...)`): The number of vertices assigned to any single cycle cannot exceed `K`, enforcing the logistical bound on simultaneous transplants.

5. **Symmetry breaking** (`seq_precede_chain(cycle)`): Cycle labels are ordered to reduce the number of equivalent solutions the solver must explore.

## Objective

**Maximise** the sum of `edge_weight[i, succ[i]]` over all vertices — that is, maximise the total benefit of all transplants performed across all selected exchange cycles.

## Notes

- Vertices that are not part of any productive exchange still appear in the model; they are assigned as their own successor (a self-loop with weight zero), effectively sitting out of any transplant.
- The model uses a `bin_packing` global constraint to enforce the cycle-length bound, which may be worth noting for solvers that have strong propagators for this constraint.

## Reference

Vicky Mak-Hau. _On the kidney exchange problem: cardinality constrained cycle and chain problems on directed graphs: a survey of integer programming approaches._ Journal of Combinatorial Optimization, **33**:35–59, 2017. [https://doi.org/10.1007/s10878-015-9932-4](https://doi.org/10.1007/s10878-015-9932-4)

Model authors: Edward Lam (Monash University) and Vicky Mak-Hau (Deakin University).
