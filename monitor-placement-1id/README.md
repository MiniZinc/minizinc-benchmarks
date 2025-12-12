# Monitor Placement for 1-Identifiability

## Overview

This MiniZinc model addresses the **monitor placement problem** in a network to ensure **1-identifiability**. The goal is to place monitors on nodes such that every node in the network can be uniquely identified based on the measurement paths. This is crucial for network monitoring and fault detection.

The network consists of:

- **Nodes**: Points in the network where monitors can be placed.
- **Routes**: Paths that connect nodes and can be used for measurements.
- **Biconnected Components**: Subgraphs that require special consideration for redundancy.

The objective is to **minimise the number of monitors** while satisfying coverage and identifiability constraints.

---

## Key Concepts

- **1-Identifiability**: Each node must be distinguishable from every other node using the available measurement paths.
- **Measurement Path**: A route that can be used for monitoring if both its endpoints have monitors.
- **Leaf Nodes**: Nodes that are independent and must always have monitors.
- **Biconnected Components**: Components with one articulation point that require at least one monitor for coverage.

---

## Parameters

- `int: n`  
  Number of nodes in the network.

- `int: r`  
  Number of routes (paths) in the network.

- `int: b`  
  Number of biconnected components with only one articulation point.

- `array[1..r,1..2] of int: routes_ends`  
  Start and end nodes for each route.

- `array[1..r] of set of int: routes`  
  Nodes included in each route.

- `array[1..b] of set of int: bi_comp`  
  Nodes in each biconnected component.

- `array[int] of int: leaf_nodes`  
  Nodes that must have monitors.

---

## Decision Variables

- `array[1..n] of var bool: x`  
  Indicates whether a monitor is placed on node `i` (`true` if monitor is placed).

- `array[1..r] of var bool: y`  
  Indicates whether a route is used as a measurement path (`true` if active).

---

## Constraints

1. **Route Activation**:

`y[path] <-> (x[start] /\ x[end])`

2. **Coverage**:  
   Every node must be covered by at least one active measurement path.

3. **1-Identifiability**:  
   For every pair of nodes, there must exist a route that includes one node but not the other.

4. **Leaf Nodes**:  
   All leaf nodes must have monitors.

5. **Biconnected Components**:  
   Each component must contain at least one monitor.

---

## Objective

Minimise the total number of monitors:
`minimize(sum(x))`

---

## Output

- Number of monitors used.
- List of nodes where monitors are placed.

---

### Notes

- This model assumes the network structure and routes are provided as input.
- The redundant constraints improve solver efficiency but do not alter the solution set.

---
