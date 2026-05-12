# Network Flow Cyclic Staffing (NFC)

## Problem Description

This model solves a **cyclic workforce scheduling** (shift staffing) problem. Time is divided into a fixed number of repeating periods (e.g., hours of a day, or shifts across a week). Each worker works a **contiguous block of consecutive periods** (a shift of fixed length), and the entire schedule repeats cyclically — once the last period ends, it wraps back to the first.

Given a minimum number of workers required in each period, the goal is to find how many shifts start at each period so that:

1. The staffing level meets or exceeds demand in every period, and
2. The total number of worker-periods (sum of workers scheduled across all periods) is minimised.

Minimising the total number of worker-periods is equivalent to minimising unnecessary overstaffing above the required demand.

## Parameters

| Parameter         | Description                                          |
| ----------------- | ---------------------------------------------------- |
| `n_periods`       | Total number of time periods in one cycle            |
| `shift_periods`   | Number of consecutive periods each shift spans       |
| `worker_count[t]` | Minimum number of workers required during period `t` |

For example, in the instance `12_2_10`, there are 12 periods per cycle and shifts last 2 consecutive periods, with demand varying across the 12 periods.

## Decision Variables

| Variable    | Description                                                                  |
| ----------- | ---------------------------------------------------------------------------- |
| `w[t]`      | Actual number of workers working during period `t`                           |
| `f[t]`      | Number of workers beginning a shift at (or around) period `t`                |
| `objective` | Total worker-periods scheduled across all periods (the quantity to minimise) |

The relationship between `f` and `w` is captured by the constraint:

```
w[t] = sum over i in 1..shift_periods of f[(t + i) mod n_periods]
```

This ensures the number of workers present in any given period equals the sum of all workers whose shifts overlap that period.

## Constraints

- **Demand satisfaction**: `w[t] >= worker_count[t]` for all periods — the actual staffing must always meet or exceed the required level.
- **Shift coverage**: The link between shift starts (`f`) and workers on duty (`w`) is maintained as described above.
- **Flow conservation**: The model uses a min-cost network flow formulation (`network_flow_cost`) to enforce the cyclic structure and compute the cost (total worker-periods). All nodes in the network have zero net flow (a pure circulation), ensuring the schedule is consistent over the full cycle.

## Objective

**Minimise** `objective` — the total number of worker-periods across the cycle (i.e., the sum of `w[t]` over all periods, weighted so only actual scheduled work is counted). This drives the solver to eliminate unnecessary overstaffing while still satisfying all demand requirements.

## Network Flow Structure

The constraint problem is encoded as a **minimum-cost circulation** on a directed graph with `2 × n_periods` arcs:

- **First `n_periods` arcs**: Each arc carries flow `w[t]` (workers on duty at period `t`) and has unit cost, so they contribute directly to the objective.
- **Last `n_periods` arcs**: Each arc carries flow `f[t]` (shift starts at period `t`) with zero cost.

The arc topology encodes both the period-to-period progression and the shift-length wrap-around, ensuring the cyclic structure is respected.

## Notes / Uncertainties

- The exact indexing convention relating `f[t]` to shift _start_ periods versus shift _end_ periods may differ from what is described above; an expert familiar with the original formulation should verify this.
- The name "NFC" most likely stands for **Network Flow Cyclic** (staffing), reflecting the solution technique used.
- This problem appeared in the **MiniZinc Challenge 2016** and **2022**.

## References

The cyclic workforce scheduling problem is a classic in operations research. Relevant foundational work includes:

- Dantzig, G. B. (1954). A comment on Edie's traffic delays at toll booths. _Operations Research_, 2(3), 339–341.
- Edie, L. C. (1954). Traffic delays at toll booths. _Operations Research_, 2(2), 107–138.
- Balakrishnan, N., & Wong, R. T. (1990). A network model for the rotating workforce scheduling problem. _Networks_, 20(1), 25–42.
- Burns, R. N., & Carter, M. W. (1985). Work force size and single shift schedules with variable demands. _Management Science_, 31(5), 599–607.

## Model update summary

Added concise inline comments in `nfc.mzn` around:

- the two arc groups used in the network-flow encoding,
- why only one arc group contributes to objective cost,
- and the intended interpretation of the coverage equation linking shift starts `f` to active workers `w`.
