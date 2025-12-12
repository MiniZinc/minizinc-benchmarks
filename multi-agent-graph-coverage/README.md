# Multi-Agent Graph Coverage Model

## **Overview**

This MiniZinc model addresses the **multi-agent graph coverage problem**, where multiple drones must collaboratively traverse and scan all edges of a directed graph. The goal is to minimise the overall completion time (makespan) while ensuring that every edge is scanned at least once.

---

## **Problem Description**

- **Scenario:** A set of drones operates on a directed graph. Each edge has a traversal time, and scanning an edge increases this time by a multiplier. Drones must plan routes so that:

  - All edges are scanned by at least one drone.
  - No edge is scanned twice by the same drone.
  - The total time to finish all scanning tasks (makespan) is minimised.

- **Key Challenges:**
  - Coordinating multiple drones.
  - Ensuring coverage of all edges.
  - Avoiding redundant scans and respecting traversal constraints.

---

## **Inputs**

- `enum EDGE`  
  Represents all directed edges in the graph.
- `array[EDGE] of int: length`  
  The traversal time for each edge.
- `array[EDGE] of set of EDGE: succ`  
  Successor edges reachable from a given edge.
- `array[EDGE] of EDGE: reverse`  
  The reverse edge corresponding to each edge.
- `int: n`  
  Number of drones.
- `int: scanmultiplier`  
  Factor by which scanning increases traversal time.

Derived sets:

- `set of int: DRONE = 1..n`  
  Drone identifiers.
- `set of int: TIME = 0..makespan`  
  Time horizon based on estimated makespan.

---

## **Decision Variables**

- `array[DRONE, EDGEX] of var EDGEX: next`  
  The next edge in the route for each drone.
- `array[DRONE, EDGEX] of var TIME: visit`  
  Start time of traversal for each edge.
- `array[DRONE, EDGE] of var bool: scan`  
  Indicates whether a drone scans a given edge.
- `array[DRONE, EDGE] of var int: traverse`  
  Computed traversal time for each edge, considering scanning.

- `var TIME: endtime`  
  The makespan (maximum completion time across all drones).

---

## **Constraints**

1. **Route Validity:**  
   Each drone’s next edge must be either a successor, the same edge (unused), or an end marker.

   ```minizinc
   constraint forall(d in DRONE, e in EDGE)(
       next[d,R(e)] in { R(e2) | e2 in succ[e] } union { R(e), end }
   );

   ```

2. **Scanning Rules:**

   - If an edge is scanned, it must be traversed.
   - No drone scans both directions of the same edge.
   - Every edge is scanned by at least one drone.

3. **Timing Consistency:**  
   Visit times increase along the route, and traversal times respect scanning multipliers.

4. **Coverage:**  
   All edges are scanned by some drone, ensuring full coverage of the graph.

---

## **Objective**

Minimise the makespan:

```minizinc
solve minimize endtime;
```

This ensures the fastest possible completion of all scanning tasks.

---

## **Applications**

- Surveillance and inspection using multiple UAVs.
- Network maintenance and monitoring.
- Robotics path planning in constrained environments.

---

## **References**

- Original concept inspired by Peter Schneider-Kamp’s coverage problem.
- Related to multi-agent routing and graph traversal optimisation in operations research.

---
