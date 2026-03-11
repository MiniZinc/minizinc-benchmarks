# Multi-Dimensional Knapsack Problem

## Problem Description

The **Multi-Dimensional Knapsack Problem** (MDKP) is a classic combinatorial optimisation problem. It generalises the well-known 0/1 knapsack problem by introducing multiple resource constraints (called "dimensions") that must all be satisfied simultaneously.

Imagine you are packing items into a knapsack, but instead of a single weight limit, there are several independent resource limits (e.g., weight, volume, cost budget). Each item consumes some amount of each resource, and you want to select a subset of items that maximises total profit without exceeding any of the resource capacities.

This particular model is formulated as a **satisfiability (proof-of-optimality)** problem: rather than searching for the maximum profit, the known optimal profit value `z` is given as a parameter, and the model checks whether a feasible item selection achieving exactly that profit exists. This approach is used to verify optimality certificates.

## Parameters

| Parameter | Description                                                        |
| --------- | ------------------------------------------------------------------ |
| `N`       | Number of items available for selection                            |
| `M`       | Number of resource constraints (dimensions)                        |
| `a[i, j]` | Amount of resource `i` consumed by item `j` (must be non-negative) |
| `b[i]`    | Total capacity of resource `i` (must be non-negative)              |
| `c[j]`    | Profit gained by selecting item `j` (must be non-negative)         |
| `z`       | The known optimal total profit value to verify                     |

## Decision Variables

- `x[j]` — A binary variable for each item `j` (ranging over `1..N`). A value of `1` means item `j` is selected; a value of `0` means it is not selected.

## Constraints

1. **Resource capacity constraints**: For each resource dimension `i`, the total consumption of that resource by all selected items must not exceed its capacity:
   $$\sum_{j=1}^{N} a_{i,j} \cdot x_j \leq b_i \quad \forall\, i \in 1..M$$

2. **Optimality certificate**: The total profit of selected items must exactly equal the known optimal value `z`:
   $$\sum_{j=1}^{N} c_j \cdot x_j = z$$

3. **Non-negativity assertions**: The model includes runtime checks to ensure all input data values are non-negative, consistent with the standard MDKP formulation.

## Objective

This model uses `solve satisfy` — there is no explicit optimisation objective. The goal is to find any assignment of the binary variables `x` that satisfies all constraints, thereby confirming that the given optimal value `z` is achievable.

## Benchmark Instances

The included data instances (`mknap1-*` and `mknap2-*`) are drawn from the well-known OR-Library benchmark set for the multidimensional knapsack problem. For example, `mknap1-6.json` represents an instance with 50 items (`N = 50`) and 5 resource dimensions (`M = 5`).

## References

- Beasley, J. E. (1990). OR-Library: Distributing test problems by electronic mail. _Journal of the Operational Research Society_, 41(11), 1069–1072. Benchmark instances available at: http://people.brunel.ac.uk/~mastjjb/jeb/orlib/mknapinfo.html
- Chu, P. C., & Beasley, J. E. (1998). A genetic algorithm for the multidimensional knapsack problem. _Journal of Heuristics_, 4(1), 63–86.
