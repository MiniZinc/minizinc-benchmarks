# Capacitated Concert Hall

## Problem Description

The **Capacitated Concert Hall** problem is a scheduling and assignment problem. A venue operator manages a set of concert halls, each with a fixed seating capacity. Promoters submit booking offers for concerts, where each offer specifies a time slot, a minimum seating requirement, and a revenue price (which may be negative, indicating a cost). The operator must decide which offers to accept and which hall to assign each accepted concert to, so as to **maximise total revenue**.

Two key constraints must be satisfied:

1. **No double-booking**: Two concerts whose time slots overlap cannot be assigned to the same hall.
2. **Capacity feasibility**: A concert can only be assigned to a hall whose seating capacity meets or exceeds the concert's requirement.

Offers that are not accepted are assigned to a special "null hall" (hall 0), meaning they are simply rejected.

This problem is a variant of the classic _Interval Scheduling_ problem, extended with capacity constraints and a revenue-maximisation objective. It is related to problems studied in the operations research literature on _facility allocation_ and _revenue management_.

## Model Parameters

| Parameter        | Description                                                    |
| ---------------- | -------------------------------------------------------------- |
| `num_offers`     | The number of concert booking offers                           |
| `num_halls`      | The number of concert halls available                          |
| `start[o]`       | The start time of offer `o`                                    |
| `end[o]`         | The end time of offer `o`                                      |
| `price[o]`       | The revenue gained (or cost incurred) if offer `o` is accepted |
| `capacity[h]`    | The seating capacity of hall `h`                               |
| `requirement[o]` | The minimum seating capacity required by offer `o`             |

## Decision Variables

| Variable    | Description                                                                 |
| ----------- | --------------------------------------------------------------------------- |
| `assign[o]` | The hall assigned to offer `o` (a value of `0` means the offer is rejected) |

## Objective

**Maximise** `objective`, the total revenue from all accepted offers:

$$\text{objective} = \sum_{o \in \text{Offer}} \text{price}[o] \times (\texttt{assign}[o] > 0)$$

## Constraints

- **No overlapping assignments**: For any set of mutually overlapping offers (a _clique_ of concurrent concerts), every accepted offer in that group must be assigned to a distinct hall. The model identifies these cliques automatically from the time intervals and uses an `alldifferent_except_0` constraint to enforce this.
- **Capacity feasibility**: Each offer can only be assigned to a hall that has sufficient capacity, or to hall 0 (rejection).
- **Symmetry breaking** (optional, enabled by default): Halls that accept identical sets of offers are considered equivalent. A _value precedence_ constraint prevents the solver from exploring symmetric assignments to such equivalent halls.
- **Dominance breaking** (optional, disabled by default): If one offer strictly dominates another (it has a better price, fits in a subset of the halls the other fits in, and covers a longer time), then accepting the weaker offer without accepting the stronger one can never be optimal.

## Notes

- The model was authored by **Graeme Gange** (University of Melbourne) in April 2018.
- No specific academic paper has been identified as the direct source of this problem instance; it may have originated as a benchmark for the [MiniZinc Challenge](https://www.minizinc.org/challenge.html). If you are aware of a primary reference, please update this README.
- The `price` values may be negative, which means some concerts represent a financial loss and would only be accepted if necessary to fill time — though under pure revenue maximisation they would simply be rejected.

## Model update summary

Added concise inline comments in concert-hall-cap.mzn to clarify:

- assignment semantics for accepted vs rejected offers,
- clique construction for overlap-based hall exclusivity constraints,
- objective interpretation as total accepted offer value.
