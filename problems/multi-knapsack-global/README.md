# Multi-Dimensional Knapsack Problem

## Problem Description

The **Multi-Dimensional Knapsack Problem (MDKP)** is a classic combinatorial optimisation problem. Imagine you have a collection of items, each with a certain value (profit), and you want to fill a knapsack as profitably as possible. Unlike the standard knapsack problem, here there are **multiple resource constraints** (dimensions) — for example, limited weight _and_ limited volume _and_ limited budget — all of which must be respected simultaneously.

More concretely:

- You have **N items**, each of which can either be packed or left behind.
- Each item has a **profit** (how valuable it is).
- There are **M resource constraints** (sometimes called "knapsacks" or "dimensions"). Each constraint has a **capacity limit**.
- Every item consumes a certain amount of each resource if it is packed.
- The goal is to choose which items to pack so that the **total profit is maximised**, while ensuring the total resource usage does **not exceed the capacity** for any of the M constraints.

This is an **NP-hard** problem and a natural generalisation of the 0/1 knapsack problem. It arises in many real-world settings, such as capital budgeting, cargo loading, and resource allocation.

## Parameters

| Parameter | Description                                                                                                                                     |
| --------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| `N`       | Number of items available to pack                                                                                                               |
| `M`       | Number of resource constraints (dimensions)                                                                                                     |
| `a[M, N]` | Weight (resource consumption) of each item for each constraint. `a[i,j]` is how much of resource `i` item `j` uses.                             |
| `b[M]`    | Capacity of each resource constraint. `b[i]` is the maximum total consumption allowed for resource `i`.                                         |
| `c[N]`    | Profit of each item. `c[j]` is the value gained by packing item `j`.                                                                            |
| `z`       | The known optimal objective value (from benchmark data). This is passed to the `knapsack` global constraint as a profit bound — see note below. |

## Decision Variables

| Variable    | Description                                                                                                             |
| ----------- | ----------------------------------------------------------------------------------------------------------------------- |
| `x[N]`      | Binary array indicating which items are packed. `x[j] = 1` means item `j` is included; `x[j] = 0` means it is left out. |
| `bVar[M]`   | The total resource consumption for each constraint. `bVar[i]` is the total weight used under constraint `i`.            |
| `objective` | The total profit of the chosen items.                                                                                   |

## Objective

**Maximise** the total profit of all packed items:

$$\text{objective} = \sum_{j=1}^{N} c_j \cdot x_j$$

## Constraints

1. **Resource limits**: For each dimension `i`, the total weight of packed items must not exceed the capacity `b[i]`:
   $$\sum_{j=1}^{N} a_{i,j} \cdot x_j \leq b[i] \quad \forall i \in 1..M$$

2. **Knapsack global constraint**: For each resource dimension `i`, MiniZinc's built-in `knapsack` global constraint is applied. This encapsulates the knapsack structure and enables powerful constraint propagation.

3. **Data integrity checks**: The model asserts that all weights, capacities, and profits are non-negative.

## Note on the `z` Parameter

The parameter `z` is labelled as "normally the optimal value" and placed under "Ignored parameters" in the model. However, it is actually passed as the _total profit_ argument to each call of the `knapsack` global constraint. In MiniZinc, this argument is a variable, so passing a fixed integer effectively constrains the knapsack's internal profit computation.

The intent appears to be to provide the known optimum to the propagator to improve filtering, but this warrants review by a MiniZinc expert — in particular, whether passing the known optimal `z` as a fixed bound is intentional (e.g., to verify or certify a solution) or whether it should instead be the `objective` variable.

## Benchmark Instances

The data files follow the naming conventions of the well-known **OR-Library** MDKP benchmark sets:

- **mknap1**: Smaller instances (around 28–39 items, 2–5 constraints).
- **mknap2**: Larger instances (up to 100 items and 30 constraints).

These instances are described in:

> Beasley, J.E. (1990). _OR-Library: Distributing test problems by electronic mail._ Journal of the Operational Research Society, 41(11), 1069–1072.

The problem itself is studied extensively in the operations research literature. A foundational reference is:

> Shih, W. (1979). _A branch and bound method for the multiconstraint zero-one knapsack problem._ Journal of the Operational Research Society, 30(4), 369–378.

This benchmark set appeared in the MiniZinc Challenge in **2015** and **2019**.
