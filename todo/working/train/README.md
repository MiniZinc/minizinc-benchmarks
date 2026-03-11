# Train Rescheduling (MiniZinc) — Beginner-Friendly Explanation

## What problem is this model solving?

This model represents a **single-track train line** with multiple stations and multiple trains.
A disruption occurs: one train is delayed at a known time, for a known duration.

After that disruption, the system must build a new timetable that still respects railway safety/order rules, while trying to keep passenger travel time low.

Passengers arrive continuously at intermediate stations and all want to travel toward the final station. Trains may wait longer at stations to pick up more passengers, and can effectively leave some passengers for later trains when capacity or timing makes that better.

In short: **recover from one delay and re-plan departures/arrivals to reduce overall passenger delay**.

## Main inputs (data)

Key input parameters include:

- `n`, `m`: number of trains and number of stations.
- `distance[j]`: travel time between station `j` and `j+1`.
- `scheduledArrival`, `scheduledDeparture`: original timetable.
- `delayTrain`, `delayTime`, `delayDuration`: disruption description.
- `passengerStart`, `passengerFlow`: when passenger arrivals start and how quickly they arrive.
- `capacity`: train capacity.
- `maxTime`: global time bound used as variable domains.

## Decision variables (what the solver chooses)

The solver chooses a new operational plan using variables such as:

- `arrival[i,j]`, `departure[i,j]`: actual arrival/departure times after rescheduling.
- `sigmaLower[i,j]`, `sigmaUpper[i,j]`: time window boundaries used to partition which passengers are collected by each train at each station.
- `collect[i,j]`: passengers boarded by train `i` at station `j`.
- `load[i,j]`: cumulative onboard passengers after station `j`.
- `dwell[i,j]`: time spent waiting at station `j` (`departure - arrival`).

## Core constraints (high-level)

The model enforces several important rule groups:

1. **Railway timing basics**
   - Trains cannot depart before arrival.
   - Minimum travel time between stations must be respected.
   - Before the disruption time, departures remain as originally scheduled.

2. **Delay propagation**
   - The delayed train must absorb the disruption (either while moving or at station), so its downstream timing is pushed later.

3. **No overtaking / track order**
   - Trains leave station 1 in order.
   - At intermediate stations, train `i+1` cannot arrive too close behind train `i` (platform occupation separation).

4. **Passenger assignment and capacity**
   - `sigma` intervals partition passenger arrival time among trains.
   - Collected passengers follow flow rate × interval length.
   - Train load accumulates station by station and is bounded by capacity.
   - Boarding speed constraints tie how many can board to dwell time (piecewise rates).

## Objective (what is minimized)

Yes, this model has an objective:

- It minimizes `objective = sum(i in 1..n)(load[i,m] * arrival[i,m])`.

Interpretation for beginners:

- `load[i,m]` is how many passengers train `i` ultimately carries to the last station.
- `arrival[i,m]` is when that train reaches the last station.
- Their product contributes a passenger-time term.
- Summing over trains gives a total passenger arrival-time measure.

So the solver prefers schedules where large passenger groups arrive earlier at the destination.

## What this means in practice

The model balances two competing effects:

- Waiting longer at a station can load more passengers now,
- But waiting also delays that train’s own arrival and can affect following trains.

The optimization finds a feasible compromise under safety, order, and capacity limits.

## Uncertainty and modeling assumptions

A few points are important when interpreting results:

- Passenger arrivals are represented by constant flow rates per station, which is a simplification.
- The model assumes one known delay event (time and duration are known at rescheduling time).
- Boarding dynamics are simplified into fixed piecewise rates.
- The objective is a proxy for passenger travel quality; it does not explicitly include every real-world factor (e.g., comfort, transfer reliability, crew constraints, stochastic delays).

Because of these assumptions, results should be viewed as **decision-support schedules** rather than exact real-world predictions.

## References / provenance

- The model appears to be part of the MiniZinc benchmark set for the problem named `train`.
- In local metadata, it is associated with MiniZinc Challenge instance sets from years 2012, 2014, and 2018.
- No explicit paper citation or external bibliographic reference is embedded directly in `train.mzn` or local `metadata.json`.
