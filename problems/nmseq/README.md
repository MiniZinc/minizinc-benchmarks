# Magic Sequence (Naive Model)

## Problem Description

A **magic sequence** of length `n` is a sequence of non-negative integers `s[0], s[1], ..., s[n-1]` such that, for every index `i`, the value `s[i]` equals the number of times `i` appears in the sequence.

For example, for `n = 10`, one magic sequence is:

```
s = [6, 2, 1, 0, 0, 0, 1, 0, 0, 0]
```

- `s[0] = 6` because the digit `0` appears exactly 6 times in the sequence.
- `s[1] = 2` because the digit `1` appears exactly 2 times.
- `s[2] = 1` because the digit `2` appears exactly 1 time.
- `s[6] = 1` because the digit `6` appears exactly 1 time.
- All other entries are `0`, and indeed `0` appears 6 times.

This is a classic self-referential constraint satisfaction problem. It is widely used as a benchmark in constraint programming because it is easy to state but requires the solver to manage many interacting constraints simultaneously.

## Model Overview

This is the **naive** formulation of the magic sequence problem. It uses **reification** — that is, it expresses the counting constraint by summing Boolean (true/false) tests over all positions in the sequence. No additional implied constraints (such as those derived from the total sum of the sequence equalling `n`, or the weighted sum equalling `n`) are added. This makes the model a useful stress-test of a solver's ability to handle a large number of simple propagators efficiently: for `n = 50`, approximately 5000 propagators are required.

## Parameters

| Name | Type    | Description                 |
| ---- | ------- | --------------------------- |
| `n`  | integer | The length of the sequence. |

## Decision Variables

| Name | Domain                   | Description                                                                                                  |
| ---- | ------------------------ | ------------------------------------------------------------------------------------------------------------ |
| `s`  | `array [1..n] of 0..n-1` | The magic sequence itself. `s[i]` holds the count of how many times the value `i-1` appears in the sequence. |

> **Note:** The model uses 1-based indexing internally (indices `1..n`), so `s[i]` encodes the count of value `i-1`.

## Constraint

For every position `i` in the sequence, the value stored at `s[i]` must equal the total number of positions `j` where `s[j] == i-1`. This is expressed using a custom predicate `number_of_v`, which counts occurrences of a value in an array via reification (converting each equality test to a 0/1 integer and summing).

## Objective

This is a **satisfaction** problem — there is no optimisation objective. The goal is simply to find any sequence that satisfies the self-referential counting constraint.

## References

The magic sequence problem is a well-known benchmark in the constraint programming community. It appears in, among other places:

- P. Van Hentenryck, _Constraint Satisfaction in Logic Programming_, MIT Press, 1989.
- It is also discussed extensively in the MiniZinc tutorial and used as a teaching example in many constraint programming courses.

A more efficient formulation adds implied constraints (e.g., that the sum of all elements equals `n`, and the weighted sum `∑ i·s[i]` also equals `n`), but this model deliberately omits them to benchmark raw propagation performance.
