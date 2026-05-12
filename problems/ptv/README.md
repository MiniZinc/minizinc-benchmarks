# Passenger Assignment and Crowding Minimization (PTV)

## What problem is this model solving?

This MiniZinc model assigns each passenger trip to a train service, then evaluates how crowded each service is at each station segment.  
The goal is to **minimize crowding-related penalties** across the network.

In plain terms:

- Each passenger has a requested departure time, an origin station, and a destination station.
- The model chooses one service for each passenger.
- From those assignments, it computes how many passengers are onboard each service between stations.
- It applies a penalty when onboard load becomes high, and minimizes the total penalty.

This is a **demand-to-service assignment** model with a crowding objective.

---

## Main inputs (data)

The model expects data describing stations, lines, services, timetables, and trips:

- `stations_name`, `STATIONS`: station list and index set.
- `line_names`, `LINES`: line list and index set.
- `station_lines[st]`: which lines serve each station.
- `service_line[s]`: line used by service `s`.
- `service_schedule[s, st]`: timetable entry for service `s` at station `st` (with `0` meaning not served).
- `MAX_PAX`: upper bound for passengers onboard.
- `trips[i,1..3]`: passenger trip data, unpacked from `flat_pax` as:
  - `trips[i,1]`: desired time block,
  - `trips[i,2]`: origin station index,
  - `trips[i,3]`: destination station index.
- `forward_TW`, `backward_TW`: compatibility time-window parameters.
- `objective_type`: selects one of two crowding-penalty formulas.

---

## Decision variables

- `p[i]` (for each passenger `i`): the selected service index.
- `pax[s,st]`: number of onboard passengers on service `s` when departing station `st`.
- `objective`: total crowding penalty to minimize.

---

## Core constraints

### 1) Feasible service assignment per passenger

A passenger can only be assigned to services that:

- stop at both origin and destination,
- run on a line common to both stations,
- and satisfy a time-compatibility rule around the requested time.

If no service is available inside the time window, the model allows assignment to the **next available compatible service after the requested time**.

### 2) Onboard passenger counting

For each service/station pair:

- if the service does not stop there, `pax[s,st] = 0`;
- otherwise, `pax[s,st]` is the count of assigned passengers whose trip has started but not yet ended at that station segment.

This is implemented with MiniZinc’s `count` global constraint.

### 3) Objective computation

The model computes total penalty over all service/station pairs.

Two modes exist:

- `objective_type == 1`: **stepwise penalty tiers** (0, 10, 100, 1000, 10000) based on occupancy thresholds.
- otherwise: **piecewise linear increasing penalty**, where marginal penalty increases at higher occupancy ranges.

Then the solver minimizes `objective`.

---

## Interpreting outputs

- `p = [...]`: chosen service for each passenger.
- `objective = ...`: total crowding penalty value (lower is better under this model).

---

## Uncertainty / assumptions to keep in mind

Some semantics are inferred from code structure rather than explicit comments/specification:

- Station order appears to be numeric (`trips[i,2] <= st < trips[i,3]`) and likely represents direction along a corridor; this may not cover bidirectional or branching paths unless encoded consistently in data.
- The fallback rule picks the first future compatible service in a generated set; this assumes deterministic ordering of service indices and that at least one such service exists.
- Crowding thresholds (`265`, `529`, `663`, `800`) are hard-coded; their operational meaning (seated capacity, comfort level, safety threshold, etc.) is not documented in the model.
- `MAX_PAX` is a variable bound, but there is no explicit hard capacity violation constraint beyond the objective penalty.

---

## References

Identifiable references from the model itself:

- MiniZinc language and modeling guide: https://docs.minizinc.dev/
- Included global constraint library file: `count.mzn` (MiniZinc standard/global constraint support)

No external domain paper or data-source citation is embedded in `pax_model.mzn`, so problem-specific references are not directly identifiable from this file alone.

## Model update summary

Added concise inline comments in pax_model.mzn to clarify:

- passenger-to-service assignment and onboard-count variable semantics,
- objective interpretation as crowding penalty aggregation,
- minimization intent under time-window compatibility constraints.
