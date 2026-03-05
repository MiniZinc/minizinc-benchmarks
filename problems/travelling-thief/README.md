# Travelling Thief Problem (TTP)

## **Overview**

The Travelling Thief Problem (TTP) is a complex optimisation problem that combines two well-known problems:

- **Travelling Salesman Problem (TSP):** Visit all cities at least once, starting and ending at city 1.
- **Knapsack Problem:** Select items from cities without exceeding the knapsack capacity.

The challenge is to maximise the total profit from selected items while minimising the rental cost of the knapsack, which depends on travel time. Travel speed decreases as the knapsack becomes heavier, making the problem highly interdependent.

---

## **Problem Description**

You are given:

- A set of cities to visit.
- A set of items distributed across cities (except city 1).
- A knapsack with limited capacity.
- Travel distances between cities.
- A renting ratio that determines the cost based on travel time.

The objective is:

- Start and end at city 1.
- Visit all cities exactly once.
- Pick items without exceeding knapsack capacity.
- Maximise the combined objective:  
  **100 × total profit − rental cost**  
  where rental cost depends on travel time and speed.

---

## **Parameters**

- `enum CITY`: Set of cities.
- `enum ITEM`: Set of items.
- `int: knapsack_capacity`: Maximum weight allowed in the knapsack.
- `int: min_speed`, `int: max_speed`: Minimum and maximum travel speeds.
- `int: renting_ratio`: Ratio for calculating rental cost.
- `array[CITY, CITY] of int: distances`: Distance between cities.
- `array[ITEM] of record(int: profit, int: weight, CITY: city): items`: Item details.

Derived:

- `itemsPerCity`: Number of items per city (except city 1).
- `city_items`: Mapping of cities to their items.

---

## **Decision Variables**

- `array[ITEM] of var bool: chosen`: Indicates if an item is picked.
- `array[TIME] of var CITY: order`: Sequence of cities visited.
- `array[TIME] of var WEIGHT: weight`: Knapsack weight at each time step.
- `array[TIME] of var VELOCITY: velocity`: Travel speed at each time step.
- `var int: profit`: Total profit from chosen items.
- `var int: rental`: Total rental cost based on travel time.
- `var int: objective`: Combined optimisation goal.

---

## **Constraints**

1. **City Visit:**
   - All cities must be visited exactly once.
   - Start at city 1.
2. **Knapsack Capacity:**
   - Total weight of chosen items ≤ knapsack capacity.
3. **Weight and Speed Dynamics:**
   - Speed decreases as weight increases.
4. **Travel Time Calculation:**
   - Depends on distances and current speed.
5. **Dominance Rule:**
   - If an item is dominated by another (higher weight, lower profit), it should not be chosen unless necessary.

---

## **Objective**

Maximise:

```minizinc
objective = 100 * profit - rental;
```

---

## **Applications**

- Logistics and delivery optimisation.
- Resource allocation in transportation.
- Benchmarking for multi-component optimisation problems.

---

## **References**

- <https://sites.google.com/view/ttp-gecco2023/home>
- Related research: Bonyadi et al., _The Travelling Thief Problem: The First Steps Toward Understanding the Interdependence of Components in Combinatorial Optimization_.

---
