# Stack-Constrained Cutting Stock

## Problem Description

This MiniZinc model describes a **cutting stock problem with stack limits**.

Imagine a factory cutting standard raw material sheets (or bars) of length `s` into smaller pieces for several product types. Each product type `p` has:

- a required piece size `size[p]`, and
- a required quantity `number[p]`.

A **cutting pattern** says how one stock piece is cut: for each product, how many pieces of that product are taken from that stock piece. The same pattern may be reused several times.

The extra difficulty is the **open stack limit** `sl`. When production of a product type starts, partially completed demand for that product may need its own stack, pallet, or buffer space. If that product continues to appear across several cutting patterns, its stack stays "open" until its last pattern is processed. The model limits how many such stacks can be open at the same time.

So the task is:

> choose a set of cutting patterns, decide how many times to use each one, and arrange them so that all demand is met while never exceeding the maximum number of open stacks.

This is a natural combination of two classic themes:

- **cutting stock / bin packing style production planning**, and
- the **open stacks** sequencing idea.

## Model Parameters

The main input data are:

- `n`: number of product types
- `size[p]`: size of one piece of product `p`
- `number[p]`: demand for product `p`
- `s`: size of one stock piece
- `k`: maximum number of cutting patterns that may be considered
- `sl`: maximum number of open stacks allowed at once

## Decision Variables

The model uses three central decision variable groups:

- `x[c,p]`: how many pieces of product `p` are cut in pattern `c`
- `m[c]`: how many times pattern `c` is repeated
- `used[c]`: whether pattern `c` is used at all

It also defines helper variables:

- `patterns`: total number of used patterns
- `first[p]`: first pattern in which product `p` appears
- `last[p]`: last pattern in which product `p` appears
- `dur[p]`: how long product `p` stays active across the pattern sequence

These helper variables allow the model to express the open-stack restriction with the global `cumulative` constraint.

## Constraints

1. **Demand satisfaction**  
   For each product, the total number of produced pieces across all repeated patterns must be at least its required quantity.

2. **Pattern capacity**  
   In each pattern, the sum of cut lengths cannot exceed the stock length `s`.

3. **Open stack limit**  
   Each product occupies one unit of stack capacity from its first appearance until its last appearance in the pattern sequence. The `cumulative` constraint ensures that at most `sl` products are simultaneously active.

4. **Symmetry breaking**  
   Unused patterns are forced to appear before used ones, and related linking constraints keep `x`, `m`, and `used` consistent. These do not change the set of real solutions; they just remove equivalent reordered versions.

## Objective

The model minimizes

- `objective = sum(m)`

which is the **total number of stock pieces used**.

The comment in the model says "minimize wastage", but the actual objective is more specifically to minimize the number of stock sheets/bars consumed. Lower material waste may correlate with this, but it is not modeled directly as leftover trim loss.

## Notes and Uncertainty

A few details are worth reading with care:

- The model uses `>=` for demand, so it allows **overproduction** if that helps satisfy the other constraints.
- The open-stack behavior is encoded indirectly through `first`, `last`, and `dur`, rather than through an explicit time or sequence variable.
- The exact industrial source of this formulation is **not identified in the model file**.
- Because the active interval is modeled via `cumulative(first, dur, ...)` with `dur[p] = last[p] - first[p]`, the intended interpretation seems to be that a product occupies stack space between its first and last relevant patterns. The precise inclusive/exclusive convention depends on MiniZinc's scheduling semantics, so this beginner explanation is necessarily approximate.

Also, the model file contains an explicit search annotation, but that is solver guidance rather than part of the problem definition, so it is intentionally not explained here.

## References

The exact provenance of this benchmark is uncertain, but it is clearly related to:

- **Cutting stock problems** in operations research
- **Open stacks / open orders** style production sequencing problems
- the **MiniZinc Challenge 2019**, as indicated by [metadata.json](metadata.json)

Related background references include:

- Gilmore, P. C., & Gomory, R. E. (1961). _A linear programming approach to the cutting-stock problem_. Operations Research, 9(6), 849–859.
- Yuen, B. J. (1995). _Heuristics for sequencing cutting patterns_. European Journal of Operational Research, 84(3), 619–642.
- Faggioli, E., & Bentivoglio, C. A. (1998). _Heuristic and exact methods for the cutting sequencing problem_. European Journal of Operational Research, 110(3), 564–575.

If a more specific source for this exact MiniZinc model becomes known, this section should be updated.

## Model update summary

Added concise inline comments in stack-cutstock-cumu.mzn to clarify:

- pattern usage and repetition decision variable semantics,
- stack-limit feasibility interpretation via cumulative overlap,
- minimization intent for total stock pieces consumed.
