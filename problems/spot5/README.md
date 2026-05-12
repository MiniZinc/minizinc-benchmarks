# SPOT5 (MiniZinc model) — Beginner-friendly overview

## What problem is this model solving?

This model represents a **satellite image acquisition planning** problem for the SPOT5 earth observation satellite.

In simple terms:

- there is a set of possible photographs the satellite could take,
- each photograph has a value or priority,
- the satellite has operational limits,
- and the goal is to choose a feasible set of photographs that gives the best overall benefit.

The header comment says the original application involves:

- multiple instruments on the satellite,
- no-overlap and transition-time restrictions between successive photographs,
- limits on telemetry/data flow,
- and limits on onboard recording capacity.

So this is a **planning/scheduling** problem where we want a good observation plan without violating satellite resource constraints.

## How this MiniZinc model represents the problem

This particular MiniZinc file is a fairly **low-level encoded version** of the problem.
Instead of writing each satellite rule directly as a named constraint, it stores many allowed combinations in data tables and asks the solver to choose values consistent with those tables.

That means the model is solving the SPOT5 planning problem, but some real-world meanings are hidden inside the instance data.

## Main inputs

The data file provides:

- `num_variables`: how many decision variables there are,
- `domains[j]`: the allowed values for variable `j`,
- `costs[j]`: the penalty/weight attached to a particular choice,
- binary table constraints (`scopes2x`, `scopes2y`, `constraints2`, ...),
- ternary table constraints (`scopes3x`, `scopes3y`, `scopes3z`, `constraints3`, ...).

The binary and ternary tables list **allowed tuples** for small groups of variables.
Together, those tables encode the feasibility rules of the satellite planning problem.

## Decision variables

- `p[j]`: the main decision variables.

Each `p[j]` must take one value from its allowed domain.

From the objective, it appears that:

- `p[j] = 0` means the corresponding request/choice is **not selected** (or is rejected),
- a nonzero value means a **selected operational choice** for that request.

Because the model is table-based, the exact interpretation of each nonzero value is not written explicitly in the model file. It is likely to represent things such as an instrument, mode, or feasible acquisition option.

## Main constraints

The model has three main kinds of constraints:

1. **Domain constraints**  
   Every variable `p[j]` must take a value from `domains[j]`.

2. **Binary table constraints**  
   Some pairs of variables must take one of the allowed value pairs listed in the data.

3. **Ternary table constraints**  
   Some triples of variables must take one of the allowed value triples listed in the data.

A beginner-friendly way to read this is:

- the model does not spell out each satellite rule directly,
- instead, it says: “these combinations are allowed, everything else is forbidden.”

This is a common way to encode a complex scheduling problem when the allowed combinations have already been precomputed.

## Objective

The model **minimizes**:

`objective = sum(j) costs[j] * bool2int(p[j] = 0)`

So a cost is paid when variable `j` is assigned value `0`.

The natural interpretation is:

- assigning `0` means skipping a photograph/request,
- `costs[j]` is the penalty for skipping it,
- therefore minimizing the total penalty is equivalent to keeping as much valuable work as possible.

This matches the problem description in the header, which says the original goal is to maximize the total importance of accepted photographs.

## What to remember as a beginner

- This is a **satellite scheduling/planning** benchmark.
- The real-world rules are encoded indirectly through **table constraints**.
- The variables `p[j]` choose whether and how each request is handled.
- The optimization tries to avoid rejecting high-value requests.

## Uncertainty / assumptions

A few details are not fully explicit in the MiniZinc file itself:

- The exact real-world meaning of each variable is not named.
- The meaning of nonzero values of `p[j]` is inferred from the data encoding, not explained directly.
- The original description mentions three instruments, telemetry, and memory limits, but these are compiled into tables rather than modeled with separate named constraints here.
- The objective appears to be a weighted rejection penalty model, which is consistent with the paper description, but that interpretation is inferred from the encoding.

If a more operational explanation is needed, the instance generator or original source benchmark description would help.

## References / provenance

Identifiable references from the model header:

- E. Bensana, Michel Lemaitre, Gerard Verfaillie, **“Earth Observation Satellite Management”**, Constraints, 4(3), 293–299, 1999.
- The MiniZinc model notes that this encoding was created by **Simon de Givry**.

Additional provenance from [metadata.json](metadata.json):

- benchmark name: `spot5`
- uses the global constraint `table`
- appears in MiniZinc Challenge instance sets for 2014, 2015, and 2022.

## Model update summary

Added concise inline comments in spot5.mzn to clarify:

- assignment decision variable semantics over acquisition options,
- table-constraint feasibility interpretation for compatibility limits,
- minimization intent for weighted rejection penalties.
