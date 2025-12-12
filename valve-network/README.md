# Valve Network Planning Model

## **Overview**

This MiniZinc model solves a **valve network optimisation problem** inspired by _Advent of Code 2022 Day 16_. The task is to maximise the total pressure released by opening valves in a network within a given time horizon. Two agents (Me and Elephant) can move through the network and open valves to increase the flow rate. The complexity of the problem is controlled by the planning horizon.

---

## **Problem Description**

- The network consists of nodes (valves), each with a flow rate and connections to other nodes.
- Two agents start at the same initial node and can perform actions at each time step:
  - **Move** to a connected node.
  - **Open** the valve at their current node.
- Opening a valve increases the total flow rate for subsequent minutes.
- The objective is to maximise the cumulative flow (pressure released) over the planning horizon.

---

## **Inputs**

- `Nodes`: Set of all valves in the network.
- `first_node`: The starting node for both agents.
- `flow[node]`: Flow rate of each valve (pressure per minute when open).
- `connections[node]`: Set of nodes directly connected to `node`.
- `horizon`: Number of minutes available for planning.

Derived sets:

- `Minutes = 1..horizon`: Time steps.
- `Steps = Minutes diff {1}`: Steps after the initial minute.

---

## **Decision Variables**

- `open[node, minute]`: Boolean indicating if a valve is open at a given minute.
- `position[minute, person]`: Node where each person (Me or Elephant) is located at a given minute.
- `action[step, person]`: Action taken by each person at each step (`Move` or `Open`).
- `current_flow[minute]`: Total flow rate at each minute based on open valves.
- `checksum`: Sum of `current_flow` over all minutes (objective).

---

## **Constraints**

1. **Initial State:**

   - Both agents start at `first_node`.
   - All valves are closed at minute 1.

2. **Action Rules:**

   - If an agent opens a valve, it remains open thereafter.
   - If an agent moves, it must move to a connected node.
   - Valve states persist across steps unless opened.

3. **Flow Calculation:**
   - `current_flow[minute]` is the sum of flow rates of all open valves.

---

## **Objective**

Maximise:

```minizinc
checksum = sum(current_flow);
```

This represents the total pressure released during the planning horizon.

---

## **Applications**

- Network optimisation problems.
- Resource allocation in time-constrained environments.
- Path planning with cooperative agents.

---

## **References**

- Inspired by [Advent of Code 2022 Day 16](https://adventofcode.com/2022/day/16).
- Related concepts: Graph traversal, scheduling, and combinatorial optimisation.

---
