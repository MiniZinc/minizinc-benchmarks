# Train Scheduling (MiniZinc) — Beginner Guide

## What problem is this model solving?
This model builds a feasible timetable for multiple train services moving through a rail network.

For each service, it decides when the train arrives and departs at each stop, whether it stops at ordinary stations, and which engine is used. At the same time, it enforces practical railway limits such as platform capacity, travel times, and spacing between trains on shared track segments.

The model balances two goals:
1. Keep trains close to their preferred finishing times.
2. Avoid skipping stations that have a penalty.

---

## Main inputs (data you provide)
- **Stops and network**: stations (`STOP`), travel times, line type between stations (`SING`, `DOUB`, `QUAD`, `NONE`), platform counts.
- **Station rules**: minimum wait at each stop, station type (`ORDINARY`, `HUB`, `TERMINUS`), skip penalty.
- **Routes and services**: predefined routes, route lengths, service-to-route mapping, desired start/end times.
- **Engines**: available engines and their start locations.
- **Timing horizon**: `makespan` and minimum separation `min_sep`.

The model also contains many assertions to validate data consistency (for example, symmetric line types, non-negative waits/costs, and valid dummy-stop behavior).

---

## Decision variables (what the solver chooses)
- `arrive[s,n]`: arrival time of service `s` at route position `n`.
- `depart[s,n]`: departure time of service `s` at route position `n`.
- `wait[s,n]`: dwell time (`depart - arrive`).
- `stopped[s,n]`: whether service `s` actually stops at that position.
- `engine[s]`: engine assigned to service `s`.
- `prev[s]`: predecessor of service `s` (either another service or an engine start).
- `delay_obj`, `skip_obj`: objective components.

---

## Core constraints (high level)
- **Time flow along a route**: next arrival must be after previous departure + travel time.
- **Minimum waiting**: if a train stops, dwell time must meet station minimum.
- **Platform capacity**: number of trains waiting at a station cannot exceed platform count (`cumulative`).
- **Mandatory stops**: non-ordinary stations must be served.
- **Engine continuity**: service chains must be consistent in location and time; every predecessor is unique (`alldifferent(prev)`).
- **Track safety/separation**:
  - Double-track sections enforce directional separation.
  - Single-track sections enforce ordering between opposite directions.

---

## Objective
Yes, this model has an objective. It minimizes:

\[
\texttt{objective} = \texttt{delay\_obj} + \texttt{skip\_obj}
\]

Where:
- `delay_obj` is total absolute deviation from each service’s ideal end time.
- `skip_obj` is total penalty for skipped stops.

---

## Notes on uncertainty
- The model is clear about operational constraints, but intended real-world assumptions (for example, whether `QUAD` lines should have additional special rules) are not documented in comments.
- The predecessor variable `prev` is constrained for engine chaining, but there is no explicit narrative in the model explaining all intended dispatch policies.
- Data semantics (units for time, exact interpretation of service end preference) are inferred from variable names and constraints.

## Model update summary

Added concise inline comments in trains.mzn to clarify:

- route timing and service-assignment decision variable semantics,
- schedule, platform, and track-feasibility constraints,
- objective intent as minimizing delay and stop-skipping penalties.

---

## Identifiable references
- Primary source: model file `trains.mzn` in this folder.
- Related benchmark metadata: `metadata.json` (MiniZinc Challenge 2024 instances listed).
- A related repository README (in `problems/train-scheduling/README.md`) mentions “Musliu et al., Train Scheduling and Timetabling Problems,” but this citation is not verified inside `trains.mzn` itself.
