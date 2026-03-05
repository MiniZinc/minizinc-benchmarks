# Capacitated Vehicle Routing Problem (CVRP)

## **Overview**

This MiniZinc model solves a simplified version of the **Capacitated Vehicle Routing Problem (CVRP)**. CVRP is a classic optimisation problem in logistics and transportation, where a fleet of vehicles must deliver goods to a set of customers from a central depot. Each vehicle has a limited capacity, and the goal is to minimise the total travel distance or time while satisfying all customer demands.

---

## **Problem Description**

- **Depot and Customers:**  
  There is one depot (starting point) and multiple customer locations.
- **Vehicles:**  
  A fixed number of vehicles, each with a maximum load capacity.
- **Demands:**  
  Each customer has a predicted demand that must be fulfilled by exactly one vehicle.
- **Distances:**  
  A matrix of predicted travel times or distances between all locations (including the depot).

The objective is to **minimise the total estimated travel time (ETA)** for all vehicles while ensuring capacity and routing constraints are satisfied.

---

## **Parameters**

- `int: num_vehicles`  
  Number of vehicles available.
- `int: num_customers`  
  Number of customer locations.
- `int: total_places = num_customers + 1`  
  Total locations (customers + depot).
- `array[1..total_places, 1..total_places] of int: predicted_ETAs`  
  Travel time or distance between locations.
- `array[1..num_vehicles] of int: vehicle_capacities`  
  Capacity of each vehicle.
- `array[1..total_places] of int: predicted_demands`  
  Demand at each location (depot demand is typically zero).

---

## **Decision Variables**

- `array[1..num_vehicles, 1..total_places] of var 0..1: visit`  
  Indicates whether a vehicle visits a location (1 = yes, 0 = no).
- `array[1..num_vehicles, 1..total_places+1] of var 0..total_places+1: order`  
  Sequence of visits for each vehicle, including return to depot.
- `var int: total_ETA`  
  Total travel time for all routes (objective to minimise).

---

## **Constraints**

1. **Capacity Constraint:**  
   Each vehicle's total load cannot exceed its capacity:

   ```minizinc
   sum(c in 1..total_places)(predicted_demands[c] * visit[v, c]) <= vehicle_capacities[v];
   ```

2. **Customer Visit Constraint:**  
   Every customer is visited exactly once by one vehicle:

   ```minizinc
   sum(v in 1..num_vehicles)(visit[v, c]) = 1;
   ```

3. **Depot Start and End:**  
   Each vehicle starts and ends at the depot.

4. **Sequential Ordering:**  
   Enforces a valid route sequence for each vehicle.

---

## **Objective**

Minimise:

```minizinc
total_ETA = sum of all travel times for visited locations and return to depot.
```

---

## **Applications**

- Delivery route planning.
- Fleet management.
- Logistics optimisation for e-commerce and supply chains.

---

## **References**

- CVRP is a well-known problem in operations research and combinatorial optimisation.
- Related literature: _Vehicle Routing Problem_ by Toth & Vigo.

---
