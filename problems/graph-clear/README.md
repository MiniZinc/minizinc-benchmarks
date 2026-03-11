# Graph Clear

## Problem Description

The **Graph Clear** problem asks: given a weighted graph, in what order should the nodes be visited (cleared) so that the peak resource usage across all steps is minimised?

Imagine a contaminated network (e.g. pipes, corridors, or communication links) where each node and each edge carries a weight representing the amount of contamination or the number of agents required to handle it. A team must sweep through the graph node by node. At any given step, two kinds of costs arise:

- **Sweep cost**: When a node is cleared, resources are needed proportional to the node's own weight plus the weights of all edges connecting it to the rest of the graph.
- **Block cost**: Any edge whose two endpoints are cleared in non-consecutive steps must be "guarded" (blocked) during every intermediate step to prevent re-contamination. The guarding cost accumulates the weights of all such in-between edges.

The combined cost at each step is the sweep cost plus the block cost. The goal is to find a clearing order that **minimises the maximum combined cost** over all steps.

This problem is related to the classical _graph searching_ / _node search_ family of problems studied in graph theory and multi-robot planning. The model is adapted from the DIDP benchmark suite by Kuroiwa and Beck [[1]](#references).

---

## Input Parameters

| Parameter            | Description                                                               |
| -------------------- | ------------------------------------------------------------------------- |
| `n`                  | Number of nodes in the graph                                              |
| `node_weights`       | Weight associated with each node (e.g. contamination level)               |
| `edge_weights[i, j]` | Weight of the directed edge from node `i` to node `j`; zero means no edge |

Several derived constants are computed from these inputs:

- `m` — total number of edges (pairs with positive weight)
- `c_block` — an upper bound on the total blocking cost (sum of all edge weights)
- `c_sweep` — an upper bound on the sweep cost at any single step
- `z_ub` / `z_lb` — upper and lower bounds on the objective value

---

## Decision Variables

| Variable      | Meaning                                                                     |
| ------------- | --------------------------------------------------------------------------- |
| `var_t[i]`    | The time step at which node `i` is cleared (a permutation of all nodes)     |
| `var_s[t]`    | The sweep cost incurred at time step `t`                                    |
| `var_b[t]`    | The block cost incurred at time step `t` (sum of weights of guarded edges)  |
| `var_l[e]`    | The earlier of the two time steps at which edge `e`'s endpoints are cleared |
| `var_u[e]`    | The later of the two time steps at which edge `e`'s endpoints are cleared   |
| `var_i[e, t]` | `true` if edge `e` must be guarded (blocked) during time step `t`           |
| `var_z`       | The objective: the maximum combined cost over all time steps                |

---

## Constraints

1. **Permutation**: Each node is cleared at a distinct time step (`all_different(var_t)`).
2. **Sweep cost**: At the time step when node `i` is cleared, the sweep cost equals the node weight plus the total weight of all edges incident to `i` (in both directions).
3. **Edge interval**: For each edge, `var_l` and `var_u` record the time steps at which its two endpoints are cleared (the lower and upper of the two).
4. **Guarding**: An edge must be guarded at every intermediate time step — i.e. every step strictly between when its two endpoints are cleared and when neither endpoint is being cleared at that step.
5. **Block cost**: The block cost at each time step is the total weight of all edges that are being guarded at that step.

---

## Objective

Minimise `var_z`, defined as:

$$\text{var\_z} = \max_{t} \bigl(\text{var\_s}[t] + \text{var\_b}[t]\bigr)$$

This minimises the **peak resource usage** across the entire clearing sequence.

---

## References

1. Kuroiwa, R., & Beck, J. C. (2023). _Domain-Independent Dynamic Programming: Generic State Space Search in Heuristic Search_. Proceedings of ICAPS. Source model: [didp-models/graph-clear](https://github.com/Kurorororo/didp-models/tree/main/graph-clear).
2. LaPaugh, A. S. (1993). _Recontamination does not help to search a graph_. Journal of the ACM, 40(2), 224–245.
3. Koloun, S., & Megiddo, N. (1998). _Cops and robbers is EXPTIME-complete_. (Background on graph searching complexity.)
