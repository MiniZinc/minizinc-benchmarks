# tdtsp — Time-Dependent Traveling Salesperson with Time Windows/Restrictions

## What problem is this model solving?
This MiniZinc model represents a **time-dependent routing/scheduling problem**. You need to visit a set of locations (or tasks), where:

- each visit has a service duration,
- travel times between visits depend on the current time,
- some visits must happen before others (precedence constraints),
- some visits are not allowed during certain time intervals (forbidden intervals).

The model builds one complete tour/order of visits and computes feasible start times for each visit.

## Inputs (high level)
The key inputs are:

- `n`: number of visits.
- `D[i]`: duration of visit `i`.
- `prec`: precedence pairs (`a` before `b`).
- `T[i,j,k]`: travel time from `i` to `j` when departing in time-step bucket `k`.
- `l`, `steps`: define discrete time buckets and total horizon.
- `which`, `interval`: forbidden time intervals for selected visits.

There are also two special nodes in the index set (`1..n+1`):
- `1` is used as the start,
- `n+1` is used as an end/dummy node so the final completion time is easy to model.

## Decision variables (what the solver chooses)
- `next[i]`, `prev[i]`: successor/predecessor of each node in the tour.
- `position[i]`: position of node `i` in the route sequence.
- `tvar[i]`: time associated with node `i` (arrival/start-style time variable).
- `objective`: equal to `tvar[n+1]` (final completion time / makespan-like endpoint).

(There is also `atposition`, mainly a channeling variable used internally in the model.)

## Core constraints (beginner view)
1. **Tour structure**
   - `next` and `prev` are inverses.
   - start/end anchors are fixed (`position[1]=1`, `position[n+1]=n+1`).
   - no self-loop (`next[i] != i`, `prev[i] != i`).

2. **Sequence consistency**
   - if `j = next[i]`, then `position[j] = position[i] + 1`.
   - similarly for predecessors.

3. **Time propagation with time-dependent travel**
   - time at a node must be at least predecessor time + predecessor service duration + travel time.
   - travel time comes from `T` using bucket `t div l`.

4. **Precedence rules**
   - for each pair `(a,b)`, finish of `a` must be before start of `b`.

5. **Forbidden intervals**
   - affected visits must either finish before the blocked interval starts or start after it ends.

6. **Redundant lower bounds**
   - extra valid inequalities tighten propagation on final completion time.

## Objective
The model **minimizes** `objective = tvar[n+1]`, i.e., the final completion time of the route.

## Notes on uncertainty and interpretation
Some semantics are inferred from variable naming and constraints (there is no inline formal problem statement in this folder):

- `tvar[i]` behaves like a start/arrival time with service and travel propagation.
- The forbidden interval encoding uses `<= start` and `>= end`; depending on intended convention, interval endpoints may be interpreted as half-open/open in practice.
- The start/end node convention (`1` and `n+1`) is model-specific and should be kept in mind when preparing data.

So this README is a **best-effort interpretation of the model code** rather than an authoritative statement from an accompanying paper.

## Identifiable references
- MiniZinc global constraint used: `inverse` (via `include "inverse.mzn"`).
- `metadata.json` indicates this model appears in MiniZinc Challenge instance sets for **2015** and **2017**.
- No explicit academic citation/DOI/source URL is present in this folder.

## Model update summary

Added concise inline comments in tdtsp.mzn to clarify:

- route, position, and time variable semantics,
- precedence and forbidden-interval feasibility constraints,
- objective intent as minimizing final completion time.
