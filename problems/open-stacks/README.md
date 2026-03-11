# Open Stacks Problem

## Problem Description

A manufacturer produces a set of **products**, each of which may be ordered by one or more **customers**. Products are manufactured one at a time, in a sequence chosen by the manufacturer. When the first product ordered by a given customer is produced, a "stack" is opened for that customer (to accumulate their goods). The stack remains open until the very last product that customer ordered has been produced, at which point the stack is closed and the order can be dispatched.

The challenge is: **in what order should the products be manufactured so that the maximum number of stacks open at any one time is as small as possible?** Minimising the peak number of open stacks reduces the floor space (or buffer capacity) needed to hold partially-completed orders.

This is a well-known combinatorial optimisation problem, sometimes called the **Open Stacks Problem (OSP)** or the **Minimising Open Orders** problem. It arises naturally in sheet-cutting, window manufacturing, and similar make-to-order industries.

## Model Parameters

| Parameter      | Description                                                           |
| -------------- | --------------------------------------------------------------------- |
| `c`            | Number of customers                                                   |
| `p`            | Number of products                                                    |
| `orders[i, j]` | Binary matrix: `1` if customer `i` ordered product `j`, `0` otherwise |

The derived value `norders[i]` counts the total number of products ordered by customer `i`.

## Decision Variables

| Variable | Description                                                                                                                       |
| -------- | --------------------------------------------------------------------------------------------------------------------------------- |
| `s[t]`   | The product manufactured at time step `t`. Together, `s[1..p]` forms a permutation of all products, i.e. the production schedule. |

## Auxiliary Variables

| Variable    | Description                                                                                                                                                                  |
| ----------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `o[i, t]`   | The number of products ordered by customer `i` that have been produced by the end of time step `t`. This tracks how much of each customer's order has been fulfilled so far. |
| `objective` | The peak number of simultaneously open stacks across all time steps.                                                                                                         |

## Constraints

1. **Each product is manufactured exactly once** — `s` must be a permutation of all products (`alldifferent`).
2. **Cumulative order tracking** — `o[i, t]` is updated at each step: when product `s[t]` is produced, every customer who ordered it has their count incremented.
3. **Stack open/closed logic** — A customer's stack is considered _open_ at time step `t` if:
   - At least one of their products has already been produced (`o[i, t] > 0`), **and**
   - At least one of their products has not yet been produced (`o[i, t-1] < norders[i]`).

   The `objective` is the maximum, over all time steps, of the count of customers whose stack is open at that step.

## Objective

**Minimise** the peak number of open stacks:

$$\text{minimise} \quad \max_{t \in 1..p} \left| \{ i \in \text{Customers} \mid o[i,\,t-1] < \text{norders}[i] \;\wedge\; o[i,\,t] > 0 \} \right|$$

## Example

Suppose there are 3 customers and 3 products:

|            | Product 1 | Product 2 | Product 3 |
| ---------- | --------- | --------- | --------- |
| Customer A | ✓         | ✓         |           |
| Customer B |           | ✓         | ✓         |
| Customer C | ✓         |           | ✓         |

If products are made in order 1 → 2 → 3:

- After step 1: stacks open for A and C (both have received product 1 but not all orders).
- After step 2: A is now complete (closed); B opens. Open stacks: B, C. Peak = 2.
- After step 3: B and C close. Peak = 2.

A different ordering might yield a peak of 3; the model finds the best.

## References

- Yuen, B. J. (1995). _Heuristics for sequencing cutting patterns_. European Journal of Operational Research, 55(2), 183–190.
- Faggioli, E., & Bentivoglio, C. A. (1998). _Heuristic and exact methods for the cutting sequencing problem_. European Journal of Operational Research, 110(3), 564–575.
- Grimes, D., & Hebrard, E. (2009). _Solving variants of the open shop scheduling problem through grouping_. Proceedings of CPAIOR 2009.
- This MiniZinc model is attributed to **Peter J. Stuckey** (2009) and has appeared as a benchmark in the [MiniZinc Challenge](https://www.minizinc.org/challenge/).
