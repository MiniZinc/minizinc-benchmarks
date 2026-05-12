# Weighted Multiset Cover (Integer)

## What problem is this model solving?
This model solves a **weighted multiset cover** problem.

- You have a set of required elements (for example, tasks, skills, or resources).
- Each element has a required amount (how many times it must be covered).
- You also have candidate “sets” that contribute some amount to each element.
- You may select multiple copies of each candidate set.
- Each candidate has a positive cost (weight).

The goal is to choose how many copies of each candidate to use so that all element requirements are met, while total cost is as small as possible.

In plain terms: **cover all needs at minimum cost, allowing repeated use of the same candidate**.

## Inputs (data)
The model expects these main inputs:

- `elements`: number of elements.
- `requirements[e]`: required coverage for each element `e`.
- `candidates`: number of candidate sets.
- `candidate_sets[c, e]`: how much candidate `c` contributes to element `e` (nonnegative).
- `candidate_weights[c]`: cost of using one copy of candidate `c` (strictly positive).

The model defines `maxreq = max(requirements)`, which is used as an upper bound for decision variables.

## Decision variables
- `candidate_copies[c]` (integer, from `0` to `maxreq`): how many copies of candidate `c` are selected.
- `objective` (integer): total weighted cost of the selected copies.

## Constraints
1. **Coverage constraints** (one per element):
   For each element `e`, the sum of contributions from all selected candidate copies must be at least `requirements[e]`.
2. **Objective definition**:
   `objective` equals the sum of `candidate_weights[c] * candidate_copies[c]` over all candidates.

Additionally, there are assertion checks to ensure:
- contribution counts are nonnegative, and
- candidate weights are positive.

## Objective
The model is a **minimization** model:

- Minimize `objective` (the total cost).

## Notes and uncertainty
- This explanation is based only on the MiniZinc model file and its inline comments.
- The file states the model/instances come from an industrial use-case, but no specific domain (e.g., logistics, staffing, manufacturing) is identified in the model itself.
- If domain-specific interpretation is needed, check instance files and project metadata.

## References
Identifiable references from the model header:

- Model by **Mikael Zayenz Lagerkvist (2021)**.
- Licensed under **MIT License**: <https://opensource.org/licenses/MIT>
- Notes indicate modifications by **MiniZinc Challenge Organisers**.

## Model update summary

Added concise inline comments in multisetcover.mzn to clarify:

- candidate-copy and cost decision variable semantics,
- multiset coverage feasibility constraints,
- objective intent as minimizing total weighted cover cost.
