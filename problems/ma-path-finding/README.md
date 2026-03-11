# Multi-Agent Path Finding (MAPF)

## Problem Description

Multi-Agent Path Finding (MAPF) is the problem of planning collision-free paths for a group of agents moving simultaneously through a shared graph (or grid map). Each agent has a designated **start node** and a **goal node**, and must travel from its start to its goal without ever sharing a node with another agent at the same time step.

This model minimises the **sum of costs** objective: the total number of time steps across all agents until each one first arrives at its goal. Agents that reach their goal early stay put for the remainder of the time horizon, so earlier arrivals reduce the objective.

MAPF is a well-studied problem in artificial intelligence and robotics, with applications in warehouse automation, video game AI, and autonomous vehicle coordination.

## Model Origin

This MiniZinc model was translated from a [Picat](http://picat-lang.org/) implementation by **Neng-Fa Zhou (2016)** by **Håkan Kjellerstrand (2017)**.

## Parameters

| Parameter  | Description                                                                                                                                      |
| ---------- | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| `k`        | Number of agents                                                                                                                                 |
| `as_len`   | Number of agents (same as `k`; used to size the agent array)                                                                                     |
| `as`       | `k × 2` array giving the **start node** (`as[a,1]`) and **goal node** (`as[a,2]`) for each agent `a`                                             |
| `makespan` | The time horizon; the model considers time steps `1` to `makespan+1`                                                                             |
| `rel_len`  | Number of nodes in the graph (also stored as `n`)                                                                                                |
| `rel`      | Adjacency structure: `rel[v]` is the set of nodes reachable from node `v` in one step (including `v` itself, allowing an agent to wait in place) |

Instance filenames follow the convention `ins_g<grid>_p<pct>_a<agents>`, where `g` is the grid size, `p` is the percentage of blocked cells, and `a` is the number of agents.

## Decision Variables

| Variable             | Description                                                                                                  |
| -------------------- | ------------------------------------------------------------------------------------------------------------ |
| `B[t, a, v]`         | Boolean indicator: equals `1` if agent `a` is at node `v` at time step `t`, and `0` otherwise                |
| `agentAtTimeT[t, a]` | The node occupied by agent `a` at time step `t` (integer version of `B`, linked by a channelling constraint) |
| `ET[a]`              | The time step at which agent `a` first arrives at its goal node                                              |
| `objective`          | The sum of all end times; this is the value being minimised                                                  |

## Constraints

1. **Initial placement**: Every agent starts at its designated start node at time step 1.
2. **Final placement**: Every agent must be at its goal node by the last time step (`makespan + 1`).
3. **Unique occupancy**: Each agent occupies exactly one node at each time step.
4. **No collisions**: No two agents may occupy the same node at the same time.
5. **Valid transitions**: An agent can only move to a node that is directly connected to its current node (according to `rel`), or stay in place.
6. **Stay at goal**: Once an agent reaches its goal, it remains there for all subsequent time steps.
7. **End-time tracking**: `ET[a]` is defined as the first time step at which agent `a` is at its goal node and stays there.

The model also includes a **redundant constraint** block (marked with `redundant_constraint`) containing an `all_different` constraint on node occupancy and the stay-at-goal rule, expressed using the `agentAtTimeT` integer variables. These help propagation but do not change the set of solutions.

## Objective

**Minimise** `objective = sum(ET)` — the sum of the arrival times of all agents at their respective goals.

## References

- Zhou, N.-F. (2016). _A Constraint-Based Approach to Multi-Agent Path Finding_ (Picat implementation). Available at [http://picat-lang.org/](http://picat-lang.org/).
- Sharon, G., Stern, R., Felner, A., & Sturtevant, N. R. (2015). Conflict-based search for optimal multi-agent pathfinding. _Artificial Intelligence_, 219, 40–66.
- Stern, R., et al. (2019). Multi-Agent Pathfinding: Definitions, Variants, and Benchmarks. _Proceedings of the International Symposium on Combinatorial Search (SoCS)_.
