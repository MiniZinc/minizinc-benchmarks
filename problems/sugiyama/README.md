# Sugiyama Graph Layout

## Problem Description

This problem asks: given a **layered directed graph**, how should the nodes on each layer be ordered so that as few edges as possible cross each other?

Imagine a flowchart or organisation chart drawn with nodes arranged in horizontal rows (layers), and arrows connecting nodes between adjacent rows. When two arrows cross each other the diagram becomes harder to read. The goal is to find a node ordering that **minimises the total number of edge crossings**.

This is the core sub-problem of the **Sugiyama framework**, a widely used method for drawing directed graphs in a clear, hierarchical style.

## Input Parameters

| Parameter            | Meaning                                                          |
| -------------------- | ---------------------------------------------------------------- |
| `layers`             | Number of horizontal layers in the graph                         |
| `width[l]`           | Number of nodes on layer `l`                                     |
| `nodes`              | Total number of nodes (must equal the sum of all `width` values) |
| `edges`              | Number of directed edges                                         |
| `start[e]`, `end[e]` | The source and target node of edge `e`                           |

Edges are assumed to connect nodes on adjacent layers only (a standard Sugiyama assumption after a pre-processing step that inserts dummy nodes).

## Decision Variables

- `positions[n]` — an integer position assigned to each node `n` within its layer.  
  Nodes on the same layer receive distinct positions (i.e. a permutation of the slots available on that layer).

- `crossings[c]` — a 0/1 indicator for each candidate pair of edges: `1` if those two edges cross under the current ordering, `0` otherwise.

- `nbCrossings` — the sum of all crossing indicators; this is the value being minimised.

## How Crossings Are Counted

Two edges `(u1 → v1)` and `(u2 → v2)` on the same pair of consecutive layers **cross** when their source nodes and target nodes appear in opposite relative orders:

$$\text{pos}(u_1) < \text{pos}(u_2) \;\text{ and }\; \text{pos}(v_2) < \text{pos}(v_1)$$

or vice versa. The model also pre-computes a set of crossings that are **unavoidable** regardless of ordering (arising from certain fully-connected 4-node patterns); these are added to `nbCrossings` in the output but are not decision variables.

## Constraints

1. **Layer bounds** — every node's position falls within the slot range of its own layer.
2. **All-different within a layer** — no two nodes on the same layer share a position.
3. **Unconnected nodes first** — nodes with no edges are pinned to the lowest-numbered positions on their layer (a symmetry-breaking rule).
4. **Ordering implied by shared neighbours** — if two nodes have the same set of predecessors (or successors), their relative order is forced to match the ordering of those shared neighbours, eliminating symmetric solutions.

## Objective

$$\text{minimise} \quad \texttt{nbFullyConnected} + \texttt{nbCrossings}$$

where `nbFullyConnected` is a constant (unavoidable crossings) and `nbCrossings` is the variable part.

## Notes and Uncertainty

- The model filename is `sugiyama2.mzn`, suggesting it may be a revised version; an earlier version may exist but is not included here.
- The `metadata.json` lists the problem type as `"puzzle"` / `"sat"`, which may not fully reflect that this is actually an **optimisation** problem.
- Instance names (e.g. `g3_8_8_2`) suggest graphs with 3–5 layers and around 7–8 nodes per layer, making them small but non-trivial combinatorially.
- No explicit data-format documentation was found in the repository; the data files appear to use the standard MiniZinc `.dzn` / `.json` format.

## References

- K. Sugiyama, S. Tagawa, and M. Toda, _"Methods for Visual Understanding of Hierarchical System Structures,"_ IEEE Transactions on Systems, Man, and Cybernetics, vol. 11, no. 2, pp. 109–125, 1981. The foundational paper describing the layered graph drawing framework.
- P. Eades and N. C. Wormald, _"Edge crossings in drawings of bipartite graphs,"_ Algorithmica, vol. 11, pp. 379–403, 1994. Analysis of the crossing-minimisation sub-problem.
