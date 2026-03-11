# Multi-Agent Graph Coverage

## Problem Description

This model solves a **multi-agent graph edge coverage** problem, originally attributed to Peter Schneider-Kamp. The setting involves a team of drones (or other mobile agents) that must collectively **scan every edge** of a directed graph as quickly as possible.

Each edge in the graph has a direction and a length (representing travel time). Traversing an edge normally takes time proportional to its length, but _scanning_ an edge — performing the inspection task while traversing it — takes longer, scaled by a `scanmultiplier` factor. Every undirected connection in the graph is represented as two directed edges (one in each direction), and it is sufficient for one drone to scan either direction of each connection.

The goal is to coordinate the drones so that every edge is scanned by at least one drone, and the time at which the last drone finishes (the **makespan**) is minimised.

## Parameters

| Parameter        | Description                                                                                                                        |
| ---------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| `EDGE`           | The set of all directed edges in the graph                                                                                         |
| `length[e]`      | Travel time to traverse edge `e`                                                                                                   |
| `succ[e]`        | The set of edges that can be visited immediately after edge `e` (i.e. edges whose start matches the end of `e`)                    |
| `reverse[e]`     | The directed edge running in the opposite direction to `e`                                                                         |
| `n`              | Number of drones available                                                                                                         |
| `scanmultiplier` | Factor by which scanning multiplies an edge's traversal time (e.g. `2` means scanning takes twice as long as just passing through) |

A derived parameter `makespan` provides an upper bound on the total time, calculated from the sum of all edge lengths and the number of drones.

## Decision Variables

| Variable         | Description                                                                                                                                                                                                                            |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `next[d, e]`     | The edge that drone `d` will visit immediately after edge `e` in its tour. A drone that doesn't use edge `e` has `next[d, e] = e` (a self-loop indicating the edge is skipped). A special `end` token marks the end of a drone's tour. |
| `visit[d, e]`    | The time at which drone `d` begins traversing edge `e`. Unused edges are assigned the maximum time.                                                                                                                                    |
| `scan[d, e]`     | A boolean indicating whether drone `d` performs a scan while traversing edge `e`.                                                                                                                                                      |
| `traverse[d, e]` | The actual time drone `d` spends on edge `e`: equals `length[e]` if not scanning, or `scanmultiplier * length[e]` if scanning. This is derived from `scan`.                                                                            |
| `endtime`        | The time at which the last drone finishes its tour. This is the objective.                                                                                                                                                             |

## Constraints

- **Tour structure**: Each drone follows a valid route through the graph. It may only move from an edge to a successor edge (one that starts where the current edge ends). The route of each drone forms a single circuit (ensured via an `alldifferent` constraint on the `next` variables).
- **Consistent timing**: The visit time of each successive edge is the visit time of the current edge plus the traversal time. The start of each drone's tour begins at time 0.
- **Scanning requires traversal**: A drone can only scan an edge it actually visits (not self-looped).
- **Complete coverage**: Every undirected connection must be scanned — at least one drone must scan either direction of every edge pair.
- **No double scanning**: A drone cannot scan both an edge and its reverse (it can only travel in one direction along a connection).
- **Traversal time bound**: The combined time for a drone to traverse an edge and its reverse is bounded, preventing redundant back-and-forth travel.

## Objective

Minimise `endtime` — the time at which the last drone in the fleet completes its tour.

## Notes and Uncertainties

- The model uses a global `alldifferent` constraint on each drone's `next` array (over all edges plus the `end` token) to enforce a single-circuit structure. A commented-out alternative using `subcircuit` is also present; the current formulation differs slightly and its exact behaviour in edge cases may warrant review by an expert.
- Several ideas and alternative constraints appear commented out in the source, indicating the model is under active development. In particular, a constraint that would prevent drones from scanning the same undirected connection (i.e. more than one drone scanning the same pair) is commented out, meaning redundant scanning by different drones is currently permitted.
- The `makespan` upper bound is a heuristic estimate and may not always be tight.

## Possible Literature

This problem is a variant of the **multi-robot arc routing** or **multi-agent coverage path planning** problem on graphs. Related work includes:

- Christofides, N. (1973). _The optimum traversal of a graph_. Omega, 1(6), 719–732. (Classic arc routing foundation.)
- Bektas, T. (2006). _The multiple traveling salesman problem: an overview of formulations and solution procedures_. Omega, 34(3), 209–219. (Background on multi-agent tour problems.)
- Corberán, Á., & Laporte, G. (Eds.). (2015). _Arc Routing: Problems, Methods, and Applications_. SIAM. (Comprehensive reference for arc routing.)

The specific formulation — with directed edges, a scan/traverse distinction, and a makespan objective — most closely resembles inspection or surveillance variants of arc routing. If the problem originates from an academic publication by Peter Schneider-Kamp (University of Southern Denmark), the original reference has not been identified with certainty and should be verified.
