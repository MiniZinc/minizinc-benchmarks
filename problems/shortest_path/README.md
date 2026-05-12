# Shortest Path

## Problem Description

Given a directed weighted graph, the **Shortest Path** problem asks: what is the
least-cost route from a designated start node to a designated end node?

This is one of the most fundamental problems in combinatorial optimisation and
graph theory. Here it is modelled as a **minimum-cost network flow** problem,
which makes the structure very clean: instead of explicitly enumerating paths,
we assign a flow value to every edge and enforce that the flow is conserved at
every intermediate node.

## Model Overview

The model is parameterised by:

| Parameter                      | Description                       |
| ------------------------------ | --------------------------------- |
| `N`                            | Number of nodes in the graph      |
| `Start`                        | Source node (net outflow = 1)     |
| `End`                          | Destination node (net inflow = 1) |
| `M`                            | Number of directed edges (arcs)   |
| `L[e]`                         | Length (weight/cost) of edge `e`  |
| `Edge_Start[e]`, `Edge_End[e]` | Tail and head node of edge `e`    |

## Decision Variables

```
array[1..M] of var 0..1: x
```

`x[e]` is a **binary** variable: it equals `1` if edge `e` is included in the
chosen path, and `0` otherwise.

## Constraints

For every node `i`, the model enforces **flow conservation**:

$$\sum_{e\,:\,\text{Edge\_Start}[e]=i} x[e] \;-\; \sum_{e\,:\,\text{Edge\_End}[e]=i} x[e] = \begin{cases} +1 & \text{if } i = \text{Start} \\ -1 & \text{if } i = \text{End} \\ 0 & \text{otherwise} \end{cases}$$

In plain language:

- Exactly one unit of flow **leaves** the source.
- Exactly one unit of flow **arrives** at the destination.
- Every intermediate node passes flow straight through (what comes in must go out).

Together these constraints guarantee that the selected edges form a valid
(simple) path from `Start` to `End`.

## Objective

```minizinc
solve minimize sum(e in Edges)( L[e] * x[e] );
```

Minimise the total length of the selected edges — i.e. find the shortest path.

## Instances

The benchmark ships with **10 instances** (used in the MiniZinc Challenge 2008),
each with **64 nodes** and **216 directed edges**. Instances vary in edge-weight
distribution and graph structure.

## Difficulty and Uncertainty

Although the shortest path problem is solvable in polynomial time by
specialised algorithms (e.g. Dijkstra's), the MiniZinc model expresses it as a
**binary integer program**. The difficulty for a general-purpose CP/MIP solver
therefore depends on how well it exploits the network-flow structure.

> **Note:** No source beyond the model header and the MiniZinc Challenge 2008
> records has been identified. The origin of the specific instance generator is
> not documented in this repository.

## References

- Puchinger, J. (2008). _Shortest Path benchmark model_ (`sp_benchmark.mzn`).
  MiniZinc Challenge 2008, University of Melbourne.
- Dijkstra, E. W. (1959). A note on two problems in connexion with graphs.
  _Numerische Mathematik_, 1, 269–271.
- Ahuja, R. K., Magnanti, T. L., & Orlin, J. B. (1993). _Network Flows: Theory,
  Algorithms, and Applications_. Prentice Hall.

## Model update summary

Added concise inline comments in shortest_path.mzn to clarify:

- edge-selection flow decision variable semantics,
- source/sink conservation interpretation,
- minimization intent for path length.
