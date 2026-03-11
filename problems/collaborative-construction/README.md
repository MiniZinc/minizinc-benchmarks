# Collaborative Construction (MACC)

## Problem Description

The **Multi-Agent Collective Construction (MACC)** problem asks a team of autonomous agents to build a given three-dimensional structure on a grid. The agents work by picking up and placing individual blocks, one at a time, to construct the target building.

A key challenge is that the structure may have upper levels that agents cannot yet reach. To access higher levels, agents must first build **ramps** — temporary staircases made of blocks leading up to the required height — and then dismantle those ramps once construction of the intended structure is complete. At the start and end of the planning horizon, all agents are off the grid and the grid is flat (empty). The goal is to arrive at the target structure by the end.

This problem is related to work in autonomous robotics, multi-agent planning, and combinatorial optimization.

## Instance Parameters

| Parameter  | Description                                                                                 |
| ---------- | ------------------------------------------------------------------------------------------- |
| `A`        | Number of agents available                                                                  |
| `T`        | Length of the time horizon (number of time steps)                                           |
| `X`        | Width of the grid                                                                           |
| `Y`        | Depth of the grid                                                                           |
| `Z`        | Maximum height of the grid                                                                  |
| `building` | A 2D array specifying the target height at each grid cell — the structure to be constructed |

## Decision Variables

### Grid height

- **`pos_height[t, i]`** — The number of blocks stacked at grid position `i` at time step `t`. This starts at 0 everywhere (flat empty grid), changes as agents place and remove blocks, and must equal the target `building` heights by the end of the time horizon.

### Agent actions

Each grid cell can hold at most one active agent at any time. The following variables describe what each agent is doing:

- **`agent_action[t, i]`** — The action taken by the agent at position `i` at time `t`. Can be one of:
  - `UNUSED` — No agent is present at this position.
  - `MOVE` — The agent moves to an adjacent cell (or stays in place).
  - `BLOCK` — The agent performs a block operation (either picking up or placing a block at a neighbouring cell).

- **`agent_next_position[t, i]`** — Where the agent at position `i` moves to at time step `t`. Must be a neighbouring cell or the same cell.

- **`agent_block_position[t, i]`** — The neighbouring cell from which the agent at position `i` picks up or places a block.

- **`agent_carrying[t, i]`** — Whether the agent at position `i` is currently carrying a block at time `t`.

- **`agent_pickup[t, i]`** — `true` if the agent at position `i` picks up a block at time `t` (derived from `agent_action` and `agent_carrying`).

- **`agent_delivery[t, i]`** — `true` if the agent at position `i` places a block at time `t` (derived from `agent_action` and `agent_carrying`).

## Constraints

The model enforces a number of physical and logical rules:

- **Movement rules**: Agents can only move to horizontally adjacent cells, and can only climb or descend by at most one block height per step. Border cells and off-grid positions are fixed to height 0.
- **Block operations**: An agent can only pick up a block from an adjacent cell that is exactly one level higher than the agent's current position. An agent can only place a block on an adjacent cell at the same height as the agent.
- **Collision avoidance**: No two agents can occupy the same cell at the same time, and agents cannot swap positions in a single step.
- **Agent count**: The number of active agents on the grid at any time step cannot exceed `A`.
- **Start and end conditions**: All agents begin and end off the grid; the grid starts flat and must end matching the target `building` structure.
- **Height change consistency**: The height at each cell changes by exactly +1 or −1 only when an adjacent agent delivers or picks up a block there, respectively.

## Objective

The model **minimises** the total number of agent-time-steps during which an agent is active on the grid:

$$\text{minimise} \sum_{t \in TT,\; i \in \text{GRID}} \left[ \text{agent\_action}[t,i] \neq \text{UNUSED} \right]$$

This encourages solutions where agents collectively finish construction as efficiently as possible, minimising the overall work effort across all agents and time steps.

## Reference

This model is based on the following paper:

> Lam, E., Stuckey, P. J., Koenig, S., & Kumar, T. K. S. (2020). **Exact Approaches to the Multi-Agent Collective Construction Problem.** _Proceedings of the 26th International Conference on Principles and Practice of Constraint Programming (CP 2020)_.
> [https://ed-lam.com/papers/macc2020.pdf](https://ed-lam.com/papers/macc2020.pdf)

Model authored by Edward Lam ([edward.lam@monash.edu](mailto:edward.lam@monash.edu)).
