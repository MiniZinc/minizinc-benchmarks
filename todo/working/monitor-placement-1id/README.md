# Monitor Placement — 1-Identifiable Network Monitoring

## Problem Description

This model addresses the **minimum monitor placement** problem for 1-identifiable network monitoring. The goal is to select the smallest possible set of nodes in a network to act as **monitors** (measurement endpoints), such that every node in the network can be uniquely identified and located by the resulting measurement data.

In this setting, a network is modelled as a graph of nodes connected by routes (paths). A **measurement path** (also called a monitoring trail or measurement end-to-end path) becomes active when **both** of its endpoints are monitors. Packets or probes sent along a measurement path can detect properties of every intermediate node the path crosses.

A network is said to be **1-identifiable** if, for every pair of distinct nodes, there exists at least one active measurement path that passes through one node but not the other. In other words, no two nodes have exactly the same "footprint" across all active measurement paths — each node has a unique signature that allows it to be individually distinguished.

The practical motivation is network fault diagnosis and traffic monitoring: with a minimal number of monitoring agents deployed at network nodes, operators can still uniquely detect and localise anomalies at any point in the network.

## Parameters

| Parameter     | Description                                                                              |
| ------------- | ---------------------------------------------------------------------------------------- |
| `n`           | Total number of nodes in the network                                                     |
| `r`           | Total number of candidate routes (paths between pairs of nodes)                          |
| `b`           | Number of biconnected components that have exactly one articulation point                |
| `routes_ends` | For each route, the indices of its two endpoint nodes                                    |
| `routes`      | For each route, the set of all nodes it passes through (including endpoints)             |
| `bi_comp`     | The node sets of the biconnected components with a single articulation point             |
| `leaf_nodes`  | Nodes that do not appear as an interior node on any route; these must always be monitors |

## Decision Variables

| Variable | Type    | Description                                     |
| -------- | ------- | ----------------------------------------------- |
| `x[i]`   | Boolean | Whether node `i` is selected as a monitor       |
| `y[p]`   | Boolean | Whether route `p` is an active measurement path |

## Constraints

1. **Activation rule**: A route becomes an active measurement path if and only if both of its endpoint nodes are monitors. If either endpoint is not a monitor, the route carries no useful measurement data.

2. **Coverage**: Every node in the network must lie on at least one active measurement path. This ensures that no node is completely invisible to all measurements.

3. **1-identifiability**: For every pair of distinct nodes A and B, there must be at least one active measurement path that covers exactly one of them. This guarantees that each node has a unique measurement signature and can be told apart from every other node.

4. **Leaf node monitors** _(redundant constraint)_: Any node that never appears as an interior node of any route (a "leaf") cannot be covered by a measurement path unless it is itself an endpoint — it must therefore be a monitor.

5. **Biconnected component coverage** _(redundant constraint)_: Each biconnected component that has only a single articulation point must contain at least one monitor, ensuring nodes in that component can be reached by measurement paths.

## Objective

**Minimise** the total number of monitors:

$$\min \sum_{i=1}^{n} x_i$$

## Notes

- The two redundant constraints (leaf nodes and biconnected components) do not change the set of feasible solutions but help the solver prune the search space more efficiently.
- This problem is related to the broader literature on **network tomography** and **identifying codes** in graphs. The 1-identifiability condition is closely connected to work on monitor placement for end-to-end network measurement (see, e.g., Bejerano & Rastogi, _Robust Monitoring of Link States in MPLS/IP Networks_, IEEE INFOCOM 2003, and later work on identifying codes for network monitoring).
- If you are familiar with the specific paper or dataset this instance originates from, please update this README with the appropriate citation.
