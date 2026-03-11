# TPP (Asymmetric Travelling Purchaser Problem)

## What problem is this model solving?

This MiniZinc model represents a **Travelling Purchaser Problem (TPP)** with asymmetric travel costs on a grid-like city network.

You need to make two linked decisions:

1. **Where to buy each product** (each city sells products at different prices), and
2. **Which cities to visit, and in what order** (travel costs differ by direction, so going A→B may cost differently from B→A).

The goal is to minimize:

- total **travel cost** between visited cities, plus
- total **purchase cost** of all required products.

A special “last city” is used as a required visited city (commented in the model as the start city), and that city sells no products.

---

## Data and parameters

The model expects the following inputs:

- `numproducts`: number of products that must be bought.
- `numcities`: number of cities in the travel network.
- `maxprice`: upper bound used for purchase-cost variable domains.
- `maxdist`: upper bound used for travel-cost variable domains.
- `dist[city1, city2]`: travel distance/cost matrix.
  - `-1` means travel is not allowed on that arc.
- `price[city, product]`: price of each product at each city (defined only for cities `1..numcities-1`, because the last city has no products).

---

## Decision variables (beginner view)

- `succ[city]`: the **next city visited after `city`**.
  - Together, all `succ` values define the tour/subtour structure.
- `travelCost[city]`: cost of traveling from `city` to `succ[city]`.
- `purchaseLoc[product]`: city where that product is bought.
- `purchaseCost[product]`: cost paid for that purchased product at its chosen city.
- `objective`: total cost to minimize.

---

## Objective

The objective is:

\[
\text{objective} = \sum_{city} \text{travelCost}[city] + \sum_{product} \text{purchaseCost}[product]
\]

So the solver balances cheaper product prices against extra travel, and vice versa.

---

## Core constraints (plain English)

1. **Travel cost consistency**  
   For each city, `travelCost[city]` must equal `dist[city, succ[city]]`.

2. **Purchase cost consistency**  
   For each product, `purchaseCost[product]` must equal the corresponding entry in `price` at the chosen purchase city.

3. **Can only buy at visited cities**  
   If a product is purchased at city `c`, then city `c` must be on the route (encoded by forbidding `succ[c] = c`, i.e., city `c` cannot be skipped as a self-loop).

4. **Route structure**  
   `subcircuit(succ)` enforces that successors form a valid subcircuit structure over cities.

5. **Required city is visited**  
   `succ[numcities] != numcities` forces the last city to be included in the route.

---

## Notes on interpretation and uncertainty

- The model comments say cities are on a grid with horizontal/vertical movement, but the MiniZinc model itself only sees the already-computed `dist` matrix. So “grid structure” is assumed to be encoded in the input data.
- The comment says “we start here” for the last city. In this model, the route is represented as a circuit (successor form), so start/end is rotationally equivalent; the important enforced fact is that the last city is included.
- The file contains a specific search annotation, but that is solver guidance rather than part of the mathematical problem definition.

---

## Identifiable references

From in-file metadata/comments:

- “Model written for the **2012 MiniZinc Challenge/competition**.”
- Problem type: **Asymmetric Travelling Purchaser Problem**.
- Author: **Kathryn Francis**.

If you want formal literature references for TPP variants, those are not explicitly listed in this file and would need external bibliographic lookup.
