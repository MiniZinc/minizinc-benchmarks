# Constrained Community Detection in Graphs

## Overview

This MiniZinc model solves the **Constrained Community Detection Problem**. The goal is to partition the nodes of a graph into groups (called _communities_) in a way that maximises a quality measure called **modularity**, while also respecting user-provided constraints about which nodes must or must not share a community.

Community detection is widely used in social network analysis, biological network clustering, and graph-based machine learning, where identifying tightly connected subgroups can reveal meaningful structure in data.

---

## Problem Description

Given a graph with `n` nodes and up to `k` communities, the task is to assign each node to a community such that:

- The **modularity** of the resulting partition is as high as possible.
- Pairs of nodes listed in the **must-link** constraints are assigned to the _same_ community.
- Pairs of nodes listed in the **cannot-link** constraints are assigned to _different_ communities.

Modularity is a well-known measure from network science that rewards partitions where there are more edges within communities than would be expected by chance in a random graph with the same degree sequence.

---

## Parameters

| Parameter     | Description                                                                                                                                                                                         |
| ------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `n`           | Number of nodes in the graph                                                                                                                                                                        |
| `k`           | Maximum number of communities allowed                                                                                                                                                               |
| `maxsize`     | Maximum number of nodes in any single community                                                                                                                                                     |
| `nML`         | Number of must-link constraint pairs                                                                                                                                                                |
| `nCL`         | Number of cannot-link constraint pairs                                                                                                                                                              |
| `ML[m, 1..2]` | The `m`-th must-link pair: these two nodes must be in the same community                                                                                                                            |
| `CL[c, 1..2]` | The `c`-th cannot-link pair: these two nodes must be in different communities                                                                                                                       |
| `A[i,j]`      | Adjacency matrix: `A[i,j] > 0` if there is an edge between nodes `i` and `j`                                                                                                                        |
| `W[i,j]`      | Weight matrix used in the modularity objective (likely the Newman-Girvan modularity matrix, where each entry reflects the edge weight adjusted for the expected number of edges between node pairs) |
| `deg[i]`      | Degree of node `i` (number of edges incident to it)                                                                                                                                                 |

---

## Decision Variables

| Variable    | Description                                                                 |
| ----------- | --------------------------------------------------------------------------- |
| `x[i]`      | The community label assigned to node `i`, an integer in `1..k`              |
| `kk`        | The number of communities actually used (equal to the maximum label in `x`) |
| `objective` | The modularity score for the partition (to be maximised)                    |

---

## Objective

The model **maximises** the `objective`, which is computed as:

$$
\text{objective} = 2 \sum_{\substack{i,j \in 1..n \\ j < i}} \mathbf{1}[x_i = x_j] \cdot W_{ij} + \sum_{i=1}^{n} W_{ii}
$$

Here, $\mathbf{1}[x_i = x_j]$ is 1 if nodes $i$ and $j$ are in the same community and 0 otherwise. In other words, the model rewards placing nodes together when the corresponding entry in `W` is positive (more internal edges than expected) and penalises doing so when it is negative.

The diagonal term (`dum = sum_i W[i,i]`) accounts for self-loop corrections in the weight matrix.

---

## Constraints

1. **Must-Link**: For each pair in `ML`, the two nodes are forced into the same community.
2. **Cannot-Link**: For each pair in `CL`, the two nodes are forced into different communities.
3. **Community size**: Each community label may be used by at most `n` nodes (and at least 0), enforced via a global cardinality constraint.
4. **Symmetry breaking**: A `value_precede_chain` constraint ensures community labels are assigned in order, eliminating equivalent solutions that differ only in how communities are numbered.

---

## Notes

- The `W` matrix is not explicitly documented in the model but, based on the objective structure and the use of `A` and `deg`, it is most likely the **Newman-Girvan modularity matrix**: $W_{ij} = A_{ij} - \frac{d_i \cdot d_j}{2m}$ (possibly scaled), where $m$ is the total number of edges. _If this interpretation is incorrect, the data files or problem source should be consulted for clarification._
- The `maxsize` parameter is declared but not explicitly used as an upper bound in the cardinality constraint (which uses `n` instead). This may be intentional or may be an unused parameter left from an earlier version of the model.

---

## References

- Newman, M. E. J. (2006). _Modularity and community structure in networks_. Proceedings of the National Academy of Sciences, 103(23), 8577–8582.
- Wagstaff, K., Cardie, C., Rogers, S., & Schrödl, S. (2001). _Constrained K-means Clustering with Background Knowledge_. ICML 2001. (Background on must-link/cannot-link constraints.)
- Guns, T., Dries, A., Tack, G., Nijssen, S., & De Raedt, L. (2013). _MiningZinc: A declarative framework for constraint-based pattern mining_. IJCAI 2013.
