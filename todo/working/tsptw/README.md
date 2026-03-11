# TSPTW (Travelling Salesperson Problem with Time Windows)

## What problem is this model solving?
This MiniZinc model solves a **routing and scheduling** problem called the **Travelling Salesperson Problem with Time Windows (TSPTW)**.

- A vehicle starts at a **depot** (location `1`),
- must visit every location exactly once,
- and return to the depot,
- while respecting each location’s allowed visit interval (`early[l]` to `late[l]`).

If the vehicle arrives too early, it can wait. If it would leave after `late[l]`, the route is invalid.

---

## Inputs (data)
The model expects:

- `numLocations`: number of locations (including the depot),
- `early[l]`: earliest allowed service/visit time at location `l`,
- `late[l]`: latest allowed service/visit time at location `l`,
- `duration[i,j]`: travel time from location `i` to location `j`.

The depot is fixed as:

- `depot = 1`

---

## Decision variables (what the solver chooses)

- `pred[l]`: predecessor of location `l` in the tour (which location is visited right before `l`).
- `arrival[l]`: arrival time at location `l`.

Derived expressions/variables:

- `durToPred[l] = duration[l, pred[l]]` (travel time from predecessor to `l`, as encoded in this model),
- `departure[l] = max(arrival[l], early[l])` for non-depot nodes (you cannot depart before service can start),
- `departurePred[l] = departure[pred[l]]`.

---

## Core constraints

1. **Time propagation**
   - For each location `l`:  
     `arrival[l] = departure[pred[l]] + durToPred[l]`

2. **Single Hamiltonian circuit**
   - `circuit(pred)` forces one cycle through all locations (visit each exactly once, then return).

3. **Time window feasibility**
   - `departure[l] <= late[l]` for all locations.

Together, these ensure a valid tour with feasible timing.

---

## Objective
The model minimizes:

- `objective = arrival[depot]`

So it tries to minimize the time when the tour gets back to the depot (equivalently, route completion time in this formulation).

---

## Notes on uncertainty and interpretation
- The model is deterministic: all travel times and time windows are fixed input values.
- Real-world uncertainty (traffic, delays, stochastic service times) is **not modeled**.
- Interpretation caveat: `durToPred[l]` is written as `duration[l, pred[l]]`; many TSP formulations use `duration[pred[l], l]`. Whether this is correct depends on how the duration matrix is defined in the data (symmetric vs directed conventions).

---

## References and provenance
- Problem family: **Travelling Salesperson Problem with Time Windows (TSPTW)**.
- Model file: `tsptw.mzn` in this folder.
- Header attribution in model: Copyright 2025 Frej Knutar Lewander (MIT-style license text included in-file).
- MiniZinc global used: `circuit` from `globals.mzn`.
