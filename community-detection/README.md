# Constrained Community Detection in Graphs

## Overview

This MiniZinc model solves the **Constrained Community Detection Problem**. The goal is to partition the nodes of a graph into communities such that:

- The **modularity** of the partition is maximised (a measure of how well the graph is divided into communities).
- Certain **must-link** and **cannot-link** constraints are satisfied:
  - **Must-link**: Specific pairs of nodes must belong to the same community.
  - **Cannot-link**: Specific pairs of nodes must belong to different communities.

This problem is widely studied in network analysis, social network clustering, and graph-based machine learning.

---

## Problem Description

Given:

- A graph represented by an **adjacency matrix** `A`.
- A maximum number of communities `max_communities`.
- Lists of node pairs that must or must not be in the same community.

We aim to assign each node to a community such that:

- Modularity is maximised.
- All constraints are respected.

---

## Key Parameters

- `A[i,j]`: Adjacency matrix indicating edges between nodes `i` and `j`.
- `NODE`: Set of all nodes in the graph.
- `N`: Number of nodes.
- `COMMUNITY`: Set of possible community labels (1..max_communities).
- `same_community`: Array of node pairs that must be in the same community.
- `diff_community`: Array of node pairs that must be in different communities.
- `k[i]`: Degree of node `i`.
- `l`: Total number of stubs (sum of all degrees).
- `B[i,j]`: Modularity matrix entry for nodes `i` and `j`.

---

## Decision Variables

- `x[i]`: Community assignment for node `i` (an integer in `COMMUNITY`).
- `objective`: Total modularity score for the partition.

---

## Objective

Maximise:

$$
\text{objective} = \sum_{i,j \in NODE, i < j, x[i] = x[j]} B[i,j]
$$

This represents the modularity contribution of pairs of nodes assigned to the same community.

The actual modularity value can be derived from:

$$
\text{modularity} = \frac{2 \times \text{objective} + \sum_{i} B[i,i]}{l^2}
$$

---

## Constraints

1. **Must-Link**: Nodes in `same_community` pairs share the same community.
2. **Cannot-Link**: Nodes in `diff_community` pairs belong to different communities.
3. **Community Size Bounds**: Each community can have between 0 and `N` nodes.
4. **Symmetry Breaking**: Uses `seq_precede_chain` to reduce redundant solutions.

---

## Notes

- Modularity is scaled by `l` to avoid fractional values.
- The model supports flexible constraints for semi-supervised community detection.
- This approach is useful for clustering in social networks, biological networks, and recommendation systems.

---

### References

- Newman, M. E. J. (2006). _Modularity and community structure in networks_. Proceedings of the National Academy of Sciences.
- Constrained community detection in graphs: Applications in semi-supervised clustering.
