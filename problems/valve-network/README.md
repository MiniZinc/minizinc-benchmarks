# Valve Network (MiniZinc) — Beginner-Friendly Overview

## What problem is this model solving?
This model plans how to operate a network of valves over a limited number of minutes.

- Each valve (node) has a **flow rate**.
- Two agents (**Me** and **Elephant**) move through the network.
- At each minute, each agent can either move to a connected node or open the valve at their current node.
- Open valves contribute flow in every minute after they are opened.

The goal is to choose actions over time so the total released flow is as large as possible.

---

## Inputs (data)
The model uses these key inputs:

- `Nodes`: the set of valve locations.
- `first_node`: where both agents start.
- `flow[node]`: flow rate of each valve.
- `connections[node]`: which nodes can be reached in one move.
- `horizon`: number of minutes in the plan.

In this file, the network and flow values are embedded directly in the model (instead of a separate `.dzn` file), and hardness is adjusted using `horizon`.

---

## Decision variables (what the solver chooses)
- `position[minute, person]`: where each agent is at each minute.
- `action[step, person]`: action at each step (`Move` or `Open`).
- `open[node, minute]`: whether a valve is open at each minute.

Derived quantity:
- `current_flow[minute]`: sum of flow rates of all valves open at that minute.
- `checksum`: total flow over all minutes, i.e. `sum(current_flow)`.

---

## Main constraints (rules)
1. **Initial state**
   - Both agents start at `first_node`.
   - All valves are initially closed.

2. **Action effects**
   - If an agent chooses `Open`, the valve at that agent’s current position becomes open.
   - If an agent chooses `Move`, they must move to one of the connected nodes.

3. **State progression over time**
   - Valve open/closed states are carried forward minute to minute, except where opening occurs.
   - A valve remains open once opened (the update rules enforce persistence).

4. **Two-agent interaction handling**
   - Combined constraints ensure both agents’ actions at a step are reflected consistently in the valve state.

---

## Objective
The model **maximizes**:

- `checksum = sum(minute in Minutes)(current_flow[minute])`

So it prefers plans that open high-flow valves early and keep them open for more minutes.

---

## Output
For each minute, it prints:
- positions of `Me` and `Elephant`,
- set of currently open valves,
- final `checksum` value.

---

## Notes on uncertainty / modeling assumptions
- The model includes the network directly in the `.mzn`; this is convenient but less reusable than a separate data file.
- Time indexing is compact (`Minutes` and `Steps`) and can be subtle for beginners; interpretation is “state tracked per minute, actions per step.”
- The intent appears to follow Advent of Code 2022 Day 16 (two-agent variant), but exact puzzle semantics (e.g., minute-by-minute timing conventions) may differ slightly depending on interpretation.
- Some constraints are written in a nontrivial way to combine both agents’ effects; equivalent formulations are possible.

---

## References
- Advent of Code 2022, Day 16: https://adventofcode.com/2022/day/16
- Commented source reference in model: https://github.com/zayenz/advent-of-code-2022
- Model author (from file header): Mikael Zayenz Lagerkvist

## Model update summary

Added concise inline comments in valve-network.mzn to clarify:

- position, action, and open-state decision variable semantics,
- minute-by-minute movement and valve-opening feasibility constraints,
- objective intent as maximizing accumulated released flow.
