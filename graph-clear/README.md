# Graph Clearing Problem

## Overview

This MiniZinc model addresses the **Graph Clearing Problem**, which involves clearing nodes and edges of a weighted graph in a specific order to minimise the total cost. The problem is inspired by scenarios such as network maintenance or cleaning tasks where each node and edge has an associated cost, and the sequence of operations affects the overall cost.

---

## Problem Description

- We are given:
  - A set of **nodes** with associated weights (`node_weights`).
  - A set of **edges** with associated weights (`edge_weights`).
- The goal is to determine an order in which nodes are cleared and compute the cost of clearing edges that lie between cleared nodes.
- The objective is to **minimise the maximum cumulative cost** incurred during the clearing process.

---

## Key Parameters

- `n`: Number of nodes in the graph.
- `NODE`: Enumeration of nodes (`Node(1..n)`).
- `node_weights[i]`: Weight (cost) of clearing node `i`.
- `edge_weights[i,j]`: Weight (cost) of clearing edge between nodes `i` and `j`.
- `m`: Number of edges with positive weight.
- `EDGE`: Enumeration of edges (`Edge(1..m)`).
- `edges`: List of edge pairs `(i,j)` where `edge_weights[i,j] > 0`.

---

## Decision Variables

- `var_t[i]`: The position (order) in which node `i` is cleared.
- `var_l[e]`, `var_u[e]`: Lower and upper bounds of positions for edge `e` based on its endpoints.
- `var_s[t]`: Sweep cost for node cleared at position `t` (node weight plus adjacent edge weights).
- `var_b[t]`: Blocking cost for node at position `t` (sum of edge weights that remain active during clearing).
- `var_i[e,t]`: Boolean indicating if edge `e` is active when clearing node at position `t`.
- `var_z`: Maximum cumulative cost across all positions.

---

## Constraints

1. **Objective Calculation**:
   - `var_z` equals the maximum of `var_s[t] + var_b[t]` over all positions `t`.
2. **Sweep Cost**:
   - For each node, its sweep cost is its weight plus the sum of weights of adjacent edges.
3. **Unique Positions**:
   - All nodes must have distinct positions (`all_different(var_t)`).
4. **Edge Activity**:
   - For each edge, determine its active range based on the positions of its endpoints.
5. **Blocking Cost**:
   - For each position, compute the sum of weights of edges that are active during that step.

---

## Objective

Minimise:
\[
\text{objective} = \text{var_z}
\]
This represents the **minimum possible maximum cumulative cost** during the clearing process.

---

## Notes

- This model is useful for optimisation in network maintenance, scheduling, and resource allocation.
- The problem is NP-hard and related to graph layout and sequencing problems.

---
