# Cyclic Hoist Scheduling Problem

## Problem Description

This model solves the **Cyclic Hoist Scheduling Problem (CHSP)**, a classic scheduling problem arising in automated manufacturing lines — most commonly in electroplating and surface treatment plants.

In such a facility, parts are moved through a series of treatment tanks in a fixed order by one or more robotic hoists (cranes) that run along a single overhead track. Each part must soak in each tank for a minimum and maximum amount of time. The process repeats in a cycle: at regular intervals, a new batch of parts enters the line and the schedule repeats.

The goal is to find a cyclic schedule that **minimises the cycle period** — the time between successive repetitions of the schedule — which directly maximises the throughput of the production line.

This model is an optimisation model. Key challenges include:

- Ensuring each part spends the correct amount of time in every tank (not too short, not too long).
- Preventing hoists from colliding with one another, since they all share the same single track and cannot pass each other.
- Coordinating multiple hoists to work efficiently without getting in each other's way.

## Parameters

| Parameter    | Description                                                                                                         |
| ------------ | ------------------------------------------------------------------------------------------------------------------- |
| `Multiplier` | A scaling factor used to create larger instances by repeating the tank sequence; `Multiplier=1` is the base problem |
| `Hoists`     | The number of hoists (cranes) available on the track                                                                |
| `Capacity`   | The maximum number of hoists that can simultaneously carry a part (an upper bound on concurrently in-flight jobs)   |
| `J`          | The total number of parts (jobs) simultaneously in the system                                                       |
| `Ninner`     | The number of treatment tanks in the base instance                                                                  |
| `tmin[i]`    | Minimum soaking time for a part in tank `i`                                                                         |
| `tmax[i]`    | Maximum soaking time for a part in tank `i`                                                                         |
| `e[i,j]`     | Travel time for an **empty** hoist moving from position `i` to position `j`                                         |
| `f[i]`       | Travel time for a hoist **carrying a part** from tank `i` to the next tank                                          |

When `Multiplier > 1`, the tank sequence is unrolled: `N = Multiplier × Ninner` tanks are used, with parameters cycling back through the base values. Empty travel times also account for extra travel between copies of the same tank.

## Decision Variables

| Variable    | Description                                                                                                                                                                          |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `r[i]`      | The **removal time** within a cycle at which a hoist picks up a part from tank `i` (i.e., when the part leaves tank `i`)                                                             |
| `objective` | The **cycle period** — the length of one full cycle; this is the quantity being minimised                                                                                            |
| `hoist[i]`  | Which hoist is responsible for removing the part from tank `i`                                                                                                                       |
| `B[i]`      | The number of **extra cycles** a part waits in tank `i` before being picked up (0 means picked up immediately in the same cycle; larger values mean the part waits for later cycles) |

The `B[i]` variables capture the idea that, in some situations, it may be beneficial for a part to soak in a tank slightly longer (across a cycle boundary) rather than being picked up immediately.

## Objective

Minimise `objective`, the cycle period. A shorter cycle period means parts are processed more frequently, increasing the throughput of the production line.

## Constraints

1. **Soaking time bounds**: Each part must spend at least `tmin[i]` and at most `tmax[i]` time units in tank `i`. The `B[i]` variable accounts for parts that soak across one or more cycle boundaries.
2. **Cycle completion**: The schedule must be consistent — the last removal must occur before the start of the next cycle.
3. **Capacity limit**: The total number of parts simultaneously in transit (carried by hoists) is bounded by `J`.
4. **No-clash — ordering**: Two hoists on the same track assigned to the same two tanks must not overlap in time: one must finish its move and clear the way before the other starts.
5. **No-clash — across cycle boundaries**: The same ordering requirement is enforced even when one hoist's action spans the end of one cycle into the start of the next.
6. **Same-tank delay**: When two consecutive tank positions are served, the timing must respect the travel-up and travel-down delays of the hoist at shared positions.
7. **Symmetry breaking**: The first hoist assignment is fixed to hoist 1, reducing equivalent solutions.

## References

This model accompanies the following publications by M. Wallace and N. Yorke-Smith:

- _A New Constraint Programming Model and Solving for the Cyclic Hoist Scheduling Problem_, CPAIOR 2020 (abstract).
- _A New Constraint Programming Model and Solving for the Cyclic Hoist Scheduling Problem_, **Constraints** journal article (same title).
- Dataset and original model files: [https://doi.org/10.4121/uuid:211d5c86-ee65-455c-a8ab-9265aab1e289](https://doi.org/10.4121/uuid:211d5c86-ee65-455c-a8ab-9265aab1e289)

> **Note**: This file differs slightly from the version at the above DOI. A constraint originally written for boolean `B` values was generalised to handle integer `B` values, as described in the Constraints journal article.

## Instance Naming Convention

Data files are named `PU_M_H_X.json`, where `M` is the `Multiplier`, `H` is the number of `Hoists`, and `X` is an instance index. For example, `PU_2_4_3.json` is instance 3 with multiplier 2 and 4 hoists.
