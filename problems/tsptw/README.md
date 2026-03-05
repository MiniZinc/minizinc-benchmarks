# Travelling Salesman Problem with Time Windows (TSPTW)

## **Overview**

This MiniZinc model solves the **Travelling Salesman Problem with Time Windows (TSPTW)**. The problem is an extension of the classic Travelling Salesman Problem (TSP), where a salesman must visit all locations exactly once and return to the starting point (the depot). In TSPTW, each location has a **time window** specifying the earliest and latest times the visit can occur.

The goal is to find a route that respects these time windows and minimises the time of arrival back at the depot.

---

## **Problem Description**

- **Locations:** A set of locations including the depot.
- **Time Windows:** Each location has an earliest (`early[l]`) and latest (`late[l]`) allowable visit time.
- **Travel Duration:** The time to travel between any two locations is given by `duration[i, j]`.
- **Depot:** The first location (index `1`) is the depot where the route starts and ends.

The objective is to minimise the **arrival time back at the depot** after visiting all locations.

---

## **Parameters**

- `int: numLocations`  
  Total number of locations (including the depot).
- `array[Locations] of int: early`  
  Earliest allowable visit time for each location.
- `array[Locations] of int: late`  
  Latest allowable visit time for each location.
- `array[Locations, Locations] of int: duration`  
  Travel time between locations.
- `int: depot = 1`  
  Index of the depot.

---

## **Decision Variables**

- `array[Locations] of var Locations: pred`  
  The predecessor of each location in the route (forms a Hamiltonian circuit).
- `array[Locations] of var int: arrival`  
  Arrival time at each location.
- `array[Locations] of var int: departure`  
  Departure time from each location, considering waiting if arriving early.
- `array[Locations] of var int: durToPred`  
  Travel time from the predecessor to the current location.
- `array[Locations] of var int: departurePred`  
  Departure time from the predecessor location.
- `var int: objective`  
  The arrival time back at the depot (to be minimised).

---

## **Constraints**

1. **Hamiltonian Circuit:**  
   All locations are visited exactly once, forming a single tour:

   ```minizinc
   constraint circuit(pred);
   ```

2. **Arrival Calculation:**  
   Arrival at each location equals departure from its predecessor plus travel time:

   ```minizinc
   arrival[l] = departurePred[l] + durToPred[l];
   ```

3. **Time Windows:**  
   Departure from each location must not exceed its latest allowable time:

   ```minizinc
   departure[l] <= late[l];
   ```

4. **Earliest Time Compliance:**  
   Departure time is the maximum of arrival time and earliest allowable time:
   ```minizinc
   departure[l] = max(arrival[l], early[l]);
   ```

---

## **Objective**

Minimise:

```minizinc
objective = arrival[depot];
```

This represents the time of return to the depot after completing the tour.

---

## **Applications**

- Vehicle routing with delivery time windows.
- Scheduling of service visits.
- Logistics and transportation planning.

---

## **References**

- TSPTW is a well-known NP-hard problem in operations research.
- Related literature: _The Travelling Salesman Problem with Time Windows_ by Savelsbergh (1992).

---
