# Seat Moving

## Problem Description

Imagine a row (or set) of seats where each seat is either occupied by a person or empty.
The seats start in some arrangement (`Start`) and must end up in a target arrangement (`Goal`).
The challenge is to find the shortest sequence of legal moves that transforms the starting
configuration into the goal configuration, while also minimising the total number of individual
person movements made along the way.

This is similar to the classic "15-puzzle" (sliding tile puzzle), but with people and seats,
and with the added twist that some people can directly swap seats with each other.

## Parameters

| Parameter  | Description                                                                                                          |
| ---------- | -------------------------------------------------------------------------------------------------------------------- |
| `S`        | Total number of seats                                                                                                |
| `P`        | Number of people to be seated (P < S, so at least one seat is always empty)                                          |
| `Start`    | Initial occupant of each seat (0 = empty)                                                                            |
| `Goal`     | Target occupant of each seat (0 = empty)                                                                             |
| `Can_swap` | Boolean flag per person: whether that person may directly swap seats with a neighbour (e.g. they have light luggage) |

## Decision Variables

| Variable       | Description                                              |
| -------------- | -------------------------------------------------------- |
| `seat[i, s]`   | Who sits in seat `s` at step `i` (0 = empty)             |
| `person[i, p]` | Which seat person `p` occupies at step `i`               |
| `step`         | The actual number of steps required to reach the goal    |
| `cost`         | Total number of individual person moves across all steps |
| `objective`    | Combined optimisation target (see Objective below)       |

The planning horizon is bounded by a computed constant `MAX_STEP = (2·S) ÷ (S − P + 1) + 1`,
which keeps the search space tractable.

## Allowed Moves

At each step, a person may move only if one of the following holds:

1. **Move to an empty seat** — the destination seat is currently unoccupied.
2. **Direct swap** — the person has `Can_swap = true` and swaps places with whoever currently
   occupies their destination seat.

Everyone not involved in a move stays in their current seat.

## Objective

The model minimises a lexicographic combination of `step` (fewer rounds is better) and
`cost` (fewer total individual moves is better):

```
objective = step × P × MAX_STEP + cost
```

This encoding ensures that reducing the number of rounds always takes priority over reducing
the total number of person movements within those rounds.

## Constraints

- The first step must exactly match `Start`; the last step must exactly match `Goal`.
- `seat` and `person` arrays are kept mutually consistent at every step.
- Each person appears at most once per step (`alldifferent_except_0` on seats;
  `alldifferent` on person positions).
- Once the goal is reached (after `step` rounds), no further changes are allowed.

## Notes on Uncertainty

- `MAX_STEP` is a heuristic upper bound. The true minimum number of steps may be considerably
  smaller; the model discovers this by solving. Using a tighter bound speeds up search but
  risks cutting off valid (longer) solutions for difficult instances.
- Instance file names follow the pattern `sm-<S>-<P>-<k>`, where `k` counts the number of
  people flagged as `Can_swap`. More swappable people generally makes the problem easier.

## References

- Submitted to the **MiniZinc Challenge 2018** (and re-used in 2021) by **Toshimitsu Fujiwara**.
- MiniZinc Challenge: <https://www.minizinc.org/challenge/>
