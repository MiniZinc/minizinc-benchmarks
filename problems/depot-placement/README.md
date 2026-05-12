# Depot Placement

## Problem Description

Two warehouses, **A** and **B**, each have their own truck and their own set of customers to serve. Normally, each truck only delivers to its own warehouse's customers. However, either truck is permitted to deliver to a customer belonging to the _other_ warehouse if it first visits a special intermediate location called the **depot**, where it either drops off or picks up goods on behalf of the other truck.

The key question the model answers is: **where should the depot be placed?** The depot can be located at any customer location or warehouse location, and its placement is itself a decision variable.

Each truck starts at its own warehouse and makes a round tour — visiting some customers (possibly including a customer from the other warehouse's territory via the depot) before returning home. Each truck may visit **at most one** customer belonging to the other warehouse per tour, meaning at most one cross-warehouse delivery can take place.

The goal is to find depot placement and routing decisions that **minimise the maximum total distance** travelled by either truck (i.e., make the worst-off truck travel as little as possible).

## Locations

Locations are numbered 1 to `TSize`, where `TSize = 2 × (PSize + 1)`:

| Location range     | Meaning                  |
| ------------------ | ------------------------ |
| `1`                | Warehouse A              |
| `2 .. PSize+1`     | Customers of warehouse A |
| `PSize+2`          | Warehouse B              |
| `PSize+3 .. TSize` | Customers of warehouse B |

`PSize` is the number of customers per warehouse and is given in the data file.

## Parameters

| Parameter | Meaning                                         |
| --------- | ----------------------------------------------- |
| `PSize`   | Number of customers belonging to each warehouse |
| `AllDist` | Distance table between every pair of locations  |

## Decision Variables

| Variable    | Meaning                                                        |
| ----------- | -------------------------------------------------------------- |
| `Depot`     | The chosen depot location (any location 1..`TSize`)            |
| `TourALoc`  | Ordered sequence of locations visited by truck A               |
| `TourBLoc`  | Ordered sequence of locations visited by truck B               |
| `ALegDist`  | Distance for each leg of truck A's tour                        |
| `BLegDist`  | Distance for each leg of truck B's tour                        |
| `ADist`     | Total distance travelled by truck A                            |
| `BDist`     | Total distance travelled by truck B                            |
| `objective` | The maximum of `ADist` and `BDist` — the value being minimised |

## Constraints

- Every customer (from both warehouses) must be visited by at least one of the two trucks.
- Each truck's tour visits distinct locations (no repeated visits to non-warehouse locations).
- Each truck starts its tour at its own warehouse.
- A truck may only visit the other warehouse's customer if it has already visited the depot earlier in its tour (to pick up the goods left by the other truck).
- Neither truck is permitted to visit the other warehouse location directly.

## Objective

Minimise `objective = max(ADist, BDist)` — the total distance of the longer of the two truck tours.

## Instances

The data files in this benchmark are derived from well-known **TSPLIB** instances (e.g., `ulysses22`, `att48`, `rat99`, `st70`, `ts225`, `a280`, `u159`), with a numeric suffix indicating the value of `PSize`. This problem appeared in the **MiniZinc Challenges** of 2010, 2011, and 2016.

## Model update summary

Added concise inline comments in `depot_placement.mzn` to clarify:

- the depot location decision variable and its role as an intermediate pick-up/drop-off point,
- the tour variables for each truck and what they represent, and
- the distance matrix used to calculate routing costs.

## Notes

- Each truck is allowed to visit at most one "foreign" customer per tour (this is a structural assumption baked into the tour size `TourLength + 1`). The model does not explicitly generalise to more than one cross-delivery per truck.
- The `AllDist` array is declared with a fixed size of `14×14`, but instances with larger `PSize` values appear to use the same array dimensions — data files should be checked to confirm this is consistent across all instances.
