# Steiner Tree Problem

## Overview

The **Steiner Tree Problem** asks: given a weighted graph and a designated subset of _terminal_ nodes, find the minimum-weight connected subgraph (a tree) that spans all terminal nodes. Unlike a plain minimum spanning tree, the solution is allowed (and sometimes forced) to include extra _Steiner nodes_ — nodes that are not terminals — if doing so reduces the total edge weight. This makes the problem significantly harder: it is **NP-hard** in general.

The model was submitted by **Diego de Uña** and appeared in the **MiniZinc Challenge 2018**.

---

## Problem Description

You are given:

- A graph with **nodes** and **edges**, each edge carrying a non-negative integer weight.
- A fixed set of **terminal nodes** that _must_ all appear in the solution tree.
- Any non-terminal node _may_ be included if it helps connect the terminals more cheaply.

The task is to select a subset of nodes and edges that:

1. Forms a valid **tree** (connected, acyclic).
2. Contains every terminal node.
3. Has **minimum total edge weight**.

---

## Parameters

| Name            | Description                                                    |
| --------------- | -------------------------------------------------------------- |
| `nbV`           | Number of nodes in the graph                                   |
| `nbE`           | Number of edges in the graph                                   |
| `nbT`           | Number of terminal nodes                                       |
| `terminals`     | The set of terminal node indices (must all appear in the tree) |
| `ws[e]`         | Weight of edge `e`                                             |
| `adj[n,e]`      | Whether node `n` is incident to edge `e`                       |
| `endnodes[e,n]` | Whether node `n` is an endpoint of edge `e`                    |

---

## Decision Variables

| Variable    | Type                     | Meaning                                                    |
| ----------- | ------------------------ | ---------------------------------------------------------- |
| `vs[n]`     | `var bool`               | `true` if node `n` is part of the solution tree            |
| `es[e]`     | `var bool`               | `true` if edge `e` is part of the solution tree            |
| `root`      | `var int` (a node index) | An arbitrary root chosen to anchor the tree structure      |
| `objective` | `var int`                | Total weight of selected edges (the value being minimised) |

---

## Constraints

- **Terminal coverage**: every node in `terminals` is forced into `vs` (i.e., `vs[t] = true`).
- **Tree structure**: the selected nodes and edges form a valid tree.  
  This is enforced by the custom predicate `my_steiner`, which internally:
  - Converts the undirected graph to a directed one (doubled edges).
  - Assigns each non-root node a unique _parent_ node and a _distance_ from the root.
  - Ensures every selected non-root node has exactly one selected parent edge.
  - Checks the classic tree identity: `|edges selected| = |nodes selected| − 1`.
  - Ensures no selected edge connects to an unselected node (`my_fzn_subgraph`).
- **Objective accounting**: `objective = Σ ws[e] × es[e]` (sum of weights over selected edges).  
  This is stated as a `redundant_constraint` alongside the `my_steiner` call to potentially aid propagation.

---

## Objective

**Minimise** `objective` — the total weight of all edges in the solution tree.

---

## How the Tree Predicate Works (high level)

The model uses a bespoke family of predicates (`my_steiner`, `my_fzn_tree`, `my_fzn_dtree`) rather than a built-in global. The comment in the model notes these were expected to be added to a future MiniZinc release under names without the `my_` prefix — it is possible that native equivalents now exist in newer versions of MiniZinc.

The key insight is converting the undirected problem into a _directed reachability_ problem: by duplicating every undirected edge in both directions and then requiring that every selected node is reachable from the chosen root via selected directed edges, the model ensures connectivity without needing an explicit cycle-breaking constraint.

---

## Uncertainty / Caveats

- The `root` variable is free (any node can be root); this symmetry is not broken explicitly by constraints, only by the search annotation.
- The predicates are hand-rolled inside the model file. Depending on the MiniZinc version in use, native `steiner` or `spanning_tree` globals may be available and potentially more efficient.
- Instance files use the `.stp.json` naming convention, suggesting they were converted from the standard **SteinLib** benchmark format (`.stp`).

---

## References

- **SteinLib** — a library of Steiner tree test instances:  
  <http://steinlib.zib.de/>
- Hwang, F. K., & Richards, D. S. (1992). _Steiner tree problems_. Networks, 22(1), 55–89.
- MiniZinc Challenge 2018: <https://www.minizinc.org/challenge2018/results2018.html>
