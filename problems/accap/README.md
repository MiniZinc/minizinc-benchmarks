# Airport Check-in Counter Allocation Problem (ACCAP)

## Problem Description

An airport has a shared pool of check-in counters that any airline may use throughout the day. Each flight operated by an airline requires a block of consecutive counters to be open for a fixed period of time before departure. The goal is to assign counter blocks to flights in a way that:

1. **No two flights use the same counter at the same time** — each counter can only serve one flight at any given moment.
2. **The peak number of counters used is kept as small as possible** — minimising the highest counter ID occupied at any point in the day.
3. **Flights belonging to the same airline are grouped close together** — passengers of the same airline should not have to walk large distances between adjacent counters.

This is a bi-objective optimisation problem. The two objectives (peak counter use and intra-airline spread) are combined into a single weighted sum that is minimised.

## Visualising the Problem

The problem can be thought of as packing rectangles into a 2D grid where:

- The **horizontal axis** represents time (check-in start times are fixed).
- The **vertical axis** represents counter IDs.
- Each flight is a rectangle whose **width** is the check-in duration and whose **height** is the number of consecutive counters required.

Rectangles must not overlap, and the objective is to pack them as low as possible (minimising peak counter use) while keeping same-airline rectangles close together.

## Parameters

| Parameter  | Description                                                                |
| ---------- | -------------------------------------------------------------------------- |
| `flights`  | Total number of flights across all airlines                                |
| `airlines` | Number of airlines                                                         |
| `times`    | Number of discrete time slots in the day                                   |
| `FA[a]`    | The set of flights belonging to airline `a`                                |
| `xCoor[f]` | The fixed start time of check-in for flight `f`                            |
| `opDur[f]` | The duration (in time slots) that check-in must remain open for flight `f` |
| `cNum[f]`  | The number of consecutive counters required for flight `f`                 |

## Decision Variables

| Variable   | Description                                                                                                                                                     |
| ---------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `yCoor[f]` | The ID of the lowest-numbered counter allocated to flight `f` (the counter block occupies counter IDs `yCoor[f]` through `yCoor[f] + cNum[f] - 1`)              |
| `D`        | The maximum counter ID used across all flights — represents the peak width of counter usage throughout the day                                                  |
| `S[a]`     | A measure of how spread out airline `a`'s check-in counters are — computed as the maximum positional gap between any two of the airline's flight counter blocks |

## Constraints

- **Non-overlapping** (`diffn`): The counter blocks assigned to different flights must not overlap in both the time and counter dimensions simultaneously. This is enforced using the `diffn` global constraint, which treats each check-in as a rectangle and ensures no two rectangles intersect.
- **Capacity**: All counters used by any flight must lie within the range `1..D`, i.e., `yCoor[f] + cNum[f] - 1 ≤ D` for every flight `f`.
- **Distance (clustering)**: For each pair of flights `f` and `g` belonging to the same airline, the positional gap between their counter blocks is bounded by `S[a]`.

## Objective

The model minimises a combined objective:

```
objective = D + sum(S[a] for all airlines a)
```

This balances two goals:

- **D**: reducing peak counter usage (operational efficiency for the airport).
- **sum(S)**: reducing the spread of same-airline flights across the counter hall (passenger convenience for airlines).

## Instances

Instances are named using the pattern `accap_a{A}_f{F}_t{T}`, where `A` is the number of airlines, `F` the number of flights, and `T` the number of time slots. This problem was used in the MiniZinc Challenge in **2019** and **2022**.

## References

- T. R. Lalita and G. S. R. Murthy, "The airport check-in counter allocation problem: A survey," _arXiv preprint arXiv:2208.13544_, 2022. <https://arxiv.org/abs/2208.13544>

## Model update summary

Added concise inline comments in `accap.mzn` to clarify:

- the key decision variables (`yCoor`, `D`, `S`) and what they represent in the problem,
- the four main constraints (C1–C4): non-overlapping, capacity, clustering, and objective definition,
- how the two objectives (peak counter use and airline clustering) are combined.
