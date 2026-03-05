# Train Scheduling Model

## **Overview**

This MiniZinc model addresses the **train scheduling problem**, which involves planning the movement of multiple train services across a railway network. The goal is to determine arrival and departure times at stations, allocate platforms, and assign engines to services while respecting operational constraints. The objective is to minimise delays and penalties for skipped stops.

---

## **Problem Description**

The railway network consists of:

- **Stops (stations)** with platforms and minimum wait times.
- **Routes** defining the sequence of stops for each service.
- **Lines** between stops, which can be single, double, or quadruple track.
- **Services** that need to be scheduled along predefined routes.
- **Engines** that start from specific locations and may transfer between services.

The schedule must satisfy:

- Travel times between stops.
- Minimum separation between trains on the same track.
- Platform capacity constraints.
- Engine assignment and transfer rules.

---

## **Key Inputs**

- `STOP`: Set of stations.
- `minimal_wait[STOP]`: Minimum wait time at each station.
- `travel_time[STOP, STOP]`: Travel time between stations (optional if not connected).
- `platform[STOP]`: Number of platforms at each station.
- `stype[STOP]`: Station type (ORDINARY, HUB, TERMINUS).
- `skip_cost[STOP]`: Penalty for skipping a station.
- `line[STOP, STOP]`: Track type between stations (SING, DOUB, QUAD, NONE).
- `ROUTE`: Set of routes, each with a sequence of stops.
- `SERVICE`: Set of train services, each assigned to a route.
- `service_start[SERVICE]`, `service_end[SERVICE]`: Time window for each service.
- `ENGINE`: Set of engines and their starting locations.
- `makespan`: End of the scheduling horizon.
- `min_sep`: Minimum separation time between trains on the same track.

---

## **Decision Variables**

- `arrive[SERVICE, STOPNO]`: Arrival time at each stop.
- `depart[SERVICE, STOPNO]`: Departure time at each stop.
- `wait[SERVICE, STOPNO]`: Waiting time at each stop.
- `stopped[SERVICE, STOPNO]`: Boolean indicating if the train stops.
- `engine[SERVICE]`: Engine assigned to each service.
- `prev[SERVICE]`: Previous service or engine for continuity.
- `delay_obj`: Total delay compared to ideal end times.
- `skip_obj`: Total penalty for skipped stops.
- `objective`: Combined cost of delays and skipped stops.

---

## **Constraints**

1. **Timing Constraints:**

   - Services start after their earliest start time.
   - Departure time ≥ arrival time + minimum wait.
   - Arrival at next stop ≥ previous departure + travel time.

2. **Platform Capacity:**

   - At any station, the number of trains occupying platforms cannot exceed capacity.

3. **Track Constraints:**

   - Single and double track segments enforce separation between trains.

4. **Engine Assignment:**

   - Engines must start from correct locations and transfer between services consistently.

5. **Stop Rules:**
   - Non-ordinary stations must always be stopped at.

---

## **Objective**

Minimise:

```minizinc
objective = delay_obj + skip_obj;
```

Where:

- `delay_obj` = sum of absolute differences between actual and ideal end times.
- `skip_obj` = sum of penalties for skipped stations.

---

## **Applications**

- Railway timetable generation.
- Resource allocation for train operations.
- Optimisation of passenger and freight train schedules.

---

## **References**

- Related literature: Musliu et al., _Train Scheduling and Timetabling Problems_.
- Practical use in railway operations and transport planning.

---
