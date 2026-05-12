# Diameter-Constrained Minimum Spanning Tree (DC-MST)

## Problem Description

Given an undirected graph with a set of nodes and weighted edges, the goal is to find a **spanning tree** of minimum total edge weight such that the **diameter** of the tree does not exceed a given limit $D$.

A spanning tree is a connected subgraph that includes every node in the graph and uses exactly $n - 1$ edges (where $n$ is the number of nodes), with no cycles. The **diameter** of a tree is the length of the longest path between any two nodes in the tree (measured by the number of edges along the path).

This problem arises naturally in network design, where a communications or distribution network must connect all sites at minimum cost while keeping the longest route between any two sites within an acceptable bound.

## Parameters

| Parameter  | Description                                                                                                      |
| ---------- | ---------------------------------------------------------------------------------------------------------------- |
| `nbV`      | Number of nodes in the graph                                                                                     |
| `nbE`      | Number of edges in the graph                                                                                     |
| `en`       | For each edge, the two endpoint nodes it connects                                                                |
| `adj`      | For each node, a boolean array indicating which edges are incident to it                                         |
| `ws`       | Non-negative integer weight of each edge                                                                         |
| `diameter` | The maximum allowed diameter $D$ of the spanning tree                                                            |
| `radius`   | Derived from the diameter as $\lfloor D/2 \rfloor$; the maximum allowed depth of any node from the tree's centre |

## Decision Variables

| Variable | Description                                                                                                                                                                                             |
| -------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `es[e]`  | Boolean: `true` if edge $e$ is included in the spanning tree                                                                                                                                            |
| `root`   | The centre of the tree. For **even** diameters this is a single node; for **odd** diameters this is a central edge (identified by its edge index), and both of its endpoints act as co-roots at depth 0 |
| `h[n]`   | The height (depth from the centre) of node $n$ in the tree; must be at most `radius`                                                                                                                    |
| `p[n]`   | The parent of node $n$ in the rooted tree                                                                                                                                                               |

## Objective

Minimise the total weight of the selected edges:

$$\text{objective} = \sum_{e \in \text{edges}} es[e] \times ws[e]$$

## Model Structure

The model enforces the constraints of a valid spanning tree and the diameter bound through a **rooted tree** representation:

1. **Spanning tree structure** — exactly $n - 1$ edges are selected.
2. **Diameter enforcement** — the tree is rooted at its centre and every node is assigned a depth. The depth of every node must not exceed the radius $\lfloor D/2 \rfloor$.
3. **Even vs. odd diameter** — the model handles the two cases differently:
   - **Even diameter**: a single root node exists at depth 0; all other nodes are strictly deeper.
   - **Odd diameter**: the centre is a single edge whose two endpoints are both at depth 0; all other nodes are strictly deeper. This correctly captures the fact that the longest path has an edge at its centre rather than a node.
4. **Parent–child linking** — the edge variables `es` are linked to the parent array `p` and depth array `h`: an edge is in the tree if and only if one of its endpoints is the parent of the other.
5. **Redundant constraints** — additional implied constraints are included to help the solver prune the search space. These encode dominance relationships between edges sharing an endpoint (a cheaper edge incident on the same node is preferred when the depth ordering allows it).

## Instance File Naming Convention

Data files follow the naming pattern `t_vXX_aYY_dZ.dzn`, where:

- `t` is the instance type: `c` for complete graph, `s` for sparse graph
- `XX` is the number of nodes
- `YY` is the number of edges
- `Z` is the required diameter bound

## References

The Diameter-Constrained Minimum Spanning Tree is a well-studied combinatorial optimisation problem. Key references include:

- Gouveia, L. and Magnanti, T. L. (2003). "Network flow models for designing diameter-constrained minimum-spanning and Steiner trees." _Networks_, 41(3), 159–173.
- Dahl, G. (1998). "The 2-hop spanning tree problem." _Operations Research Letters_, 23(1–2), 21–26.
- Santos, A. C., de Sousa, A., Alvelos, F., Dzalbs, I. (various years) — several works have applied constraint programming and integer programming to DC-MST variants.

> **Note:** The specific source or academic paper for this MiniZinc model is not definitively known. If you are aware of the original publication, please update this section.

## Model update summary

Added concise inline comments in dcmst.mzn to clarify:

- diameter enforcement through rooted depth variables (h, p),
- odd/even diameter center handling via edge-center vs node-center roots,
- purpose of redundant pruning constraints for search efficiency.
