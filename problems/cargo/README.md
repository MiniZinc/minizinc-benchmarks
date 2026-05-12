# Cargo Terminal Scheduling (Coarse Piles)

## Problem Description

This model solves a **bulk cargo terminal scheduling problem**, as found at large port facilities that handle commodities such as coal, grain, or iron ore. The terminal receives multiple vessels (ships), each carrying several **piles** of bulk cargo. Each pile must be:

1. **Stacked** — unloaded from the vessel and deposited onto a physical storage pad using a stacker machine.
2. **Reclaimed** — later retrieved from the pad using a reclaimer machine and loaded onto a conveyor or another vessel.

The challenge is to decide _when_ to stack each pile and _where_ on the storage pad to place it, subject to machine capacity limits, physical space constraints, and vessel arrival schedules, while minimising the total delay experienced by vessels waiting to be fully processed.

The "coarse piles" variant uses a coarser time discretisation (larger time steps), which reduces the size of the search space and makes finding good solutions faster at the cost of some precision.

## Sets and Parameters

| Name                             | Description                                                                 |
| -------------------------------- | --------------------------------------------------------------------------- |
| `nV`                             | Number of vessels                                                           |
| `nS`                             | Number of cargo piles (across all vessels)                                  |
| `VESSELS`                        | Set of vessel indices `1..nV`                                               |
| `PILES`                          | Set of pile indices `1..nS`                                                 |
| `eta[v]`                         | Estimated Time of Arrival (ETA) for vessel `v`                              |
| `whichV[o]`                      | The vessel that pile `o` belongs to                                         |
| `dS__[o]`                        | Stacking duration of pile `o` (in discretised time units)                   |
| `dR[o]`                          | Reclaiming duration of pile `o`                                             |
| `H`                              | Total width/length of the storage pad (spatial capacity)                    |
| `T`                              | Planning horizon (total time available)                                     |
| `stCap`                          | Stacker capacity in terms of tonnage per hour                               |
| `reclN`                          | Number of reclaimers available simultaneously                               |
| `stackbefore`                    | How many time steps before the vessel ETA stacking may begin                |
| `tMaxBetwRecl`                   | Maximum allowed gap between reclaiming consecutive piles of the same vessel |
| `delayMax`                       | Maximum delay allowed for any single vessel                                 |
| `discrStackStart`, `discrPadPos` | Discretisation step sizes for time and pad position respectively            |

## Decision Variables

| Name        | Description                                                                                      |
| ----------- | ------------------------------------------------------------------------------------------------ |
| `tS__[o]`   | Discretised start time of stacking pile `o`                                                      |
| `h__[o]`    | Discretised position of pile `o` on the storage pad                                              |
| `tR[o]`     | Start time of reclaiming pile `o`                                                                |
| `dT__[o]`   | Total duration from the start of stacking to the end of reclaiming for pile `o` (discretised)    |
| `tReady[v]` | Time at which vessel `v` has all its piles fully reclaimed (i.e., the vessel is ready to depart) |
| `objective` | Sum of delays over a central subset of vessels (see Objective below)                             |

Several derived arrays (`tS`, `dTotal`, `len`, etc.) are computed from the above for use in constraints.

## Constraints

- **Temporal ordering**: Stacking of a pile must be fully completed before reclaiming begins.
- **Arrival time**: Neither stacking nor reclaiming may begin significantly before the vessel arrives (`eta`).
- **Pile ordering**: For consecutive piles belonging to the same vessel, reclaiming must happen in order, and the gap between consecutive reclaims is bounded by `tMaxBetwRecl`.
- **Pad bounds**: Each pile must fit entirely within the pad's length (`H`) and the planning horizon (`T`).
- **No spatial overlap** (`diffn`): Piles occupy rectangular regions on the pad in the time-space plane and must not overlap — i.e., no two piles can share the same pad position at the same time.
- **Stacker capacity** (`cumulative`): The total tonnage being stacked at any point in time must not exceed the stacker's rated capacity (`stCap`).
- **Pad width** (`cumulative`): The total pad space occupied at any moment must not exceed `H`.
- **Reclaimer capacity** (`cumulative`): No more than `reclN` piles may be reclaimed simultaneously.
- **Delay bounds**: The delay for every vessel and the total sum of delays are bounded.

## Objective

The model **minimises** the sum of delays over a central subset of vessels (from vessel 6 to vessel `nV-5`, inclusive). The delay for a vessel is defined as how much later it is fully processed compared to its ideal finishing time (ETA plus total reclaiming duration).

> **Note**: The objective deliberately excludes the first 5 and last 5 vessels from the sum. This is an unusual choice — it may be to avoid boundary effects in the schedule, or it may reflect a modelling convention from the source application. The intent should be confirmed with the original problem authors.

## Notes

This problem is characteristic of **stockyard management** at bulk commodity terminals, a well-studied topic in operations research and scheduling. Related work includes scheduling models for coal export terminals (e.g., in Australian and Brazilian mining logistics) where stacker/reclaimer scheduling is a key operational challenge. The structure of the model — combining 2D non-overlapping rectangle placement with cumulative machine capacity constraints — is consistent with published approaches in this domain, though a specific academic reference for this exact formulation has not been identified.

## Model update summary

Added concise inline comments in cargo_coarsePiles.mzn to clarify:

- decision variable roles for stacking/reclaiming times and pad positions,
- distinction between discretized and scaled time variables,
- objective meaning as aggregate vessel delay minimization.
