# Maximum Directed Acyclic Graph (Maximum DAG)

## Problem Description

Given a directed graph $G = (V, E)$ with a set of nodes $V$ and directed edges $E$, the goal is to find the **largest subgraph that is a Directed Acyclic Graph (DAG)**.

A **DAG** is a directed graph that contains no directed cycles — you cannot follow a sequence of directed edges and return to the starting node. The task is to select as many edges from the original graph as possible while keeping this acyclicity property. Equivalently, this problem is the complement of the **Minimum Feedback Arc Set** problem: removing the fewest edges to eliminate all directed cycles.

This is a classic combinatorial optimisation problem and is known to be NP-hard in general. The instance files are named `xx_yy.dzn`, where `xx` is the number of nodes and `yy` is the benchmark index.

## Parameters (Input Data)

| Parameter        | Description                                                  |
| ---------------- | ------------------------------------------------------------ |
| `nbV`            | Number of nodes in the graph                                 |
| `nbE`            | Number of directed edges in the graph                        |
| `tails[e]`       | The source (tail) node of edge `e`                           |
| `heads[e]`       | The destination (head) node of edge `e`                      |
| `incident[n, e]` | `true` if node `n` is the **head** (destination) of edge `e` |
| `outgoing[n, e]` | `true` if node `n` is the **tail** (source) of edge `e`      |

## Decision Variables

| Variable      | Type              | Description                                                                                                                |
| ------------- | ----------------- | -------------------------------------------------------------------------------------------------------------------------- |
| `chosen[e]`   | `bool` per edge   | Whether edge `e` is included in the selected DAG subgraph                                                                  |
| `distance[n]` | `0..nbE` per node | The length of the longest path from the root node (node 1) to node `n` in the chosen subgraph — used to enforce acyclicity |
| `objective`   | `0..nbE`          | Total number of chosen edges (the value being maximised)                                                                   |

## How Acyclicity is Enforced

The model uses a **distance/topological-level** encoding to ensure no cycles exist among the chosen edges:

- Node 1 is designated the **root** and assigned distance 0. The comment in the model states that node 1 is assumed to be connected to all other nodes — this is an assumption about the input data.
- For every other node `a`, its distance is set to the maximum over all chosen incoming edges `b`: `distance[a] = max((distance[tail(b)] + 1) × chosen[b])`.
- This ensures that if edge `b` from node `u` to node `a` is chosen, then `distance[a] > distance[u]`. Because distances can never decrease along chosen edges, no directed cycle can exist in the chosen subgraph.

## Objective

**Maximise** the total number of chosen edges:

$$\text{objective} = \sum_{e \in E} \texttt{chosen}[e]$$

## Notes and Uncertainties

- The `outgoing` array is declared as a parameter but does not appear to be used in any constraint. It may be present for reference or for use in alternative model variants.
- The model assumes that node 1 (the root) is reachable from all other nodes or connected to all other nodes. If this does not hold for a particular instance, some nodes may have a distance of 0 even when not the root, which could affect correctness. An expert familiar with the instance generation should verify this assumption.
- For nodes with no chosen incoming edges (other than the root), the `max` expression over an empty list would be undefined in standard MiniZinc. The model implicitly assumes every non-root node has at least one incoming edge in the graph — this should be confirmed against the instance data.

## References

The Maximum Acyclic Subgraph / Minimum Feedback Arc Set problem is well studied:

- Karp, R. M. (1972). _Reducibility among combinatorial problems_. In R. E. Miller & J. W. Thatcher (Eds.), _Complexity of Computer Computations_ (pp. 85–103). Plenum Press. — Established NP-hardness of the Feedback Arc Set problem.
- Ailon, N., Charikar, M., & Newman, A. (2008). _Aggregating inconsistent information: ranking and clustering_. Journal of the ACM, 55(5), 23:1–23:27. — Approximation algorithms for the problem.

> **Note:** The specific origin or publication associated with this MiniZinc model is not known to the author of this README. If you are aware of the source, please update this section.

## Model update summary

Added concise inline comments in maximum-dag.mzn to clarify:

- edge-selection and distance variable roles,
- objective semantics as maximum acyclic edge count,
- optimization intent for largest DAG subgraph.
