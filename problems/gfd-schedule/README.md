# GFD Schedule

## Problem Description

This model solves a **group-facility-day scheduling** problem. A set of items must be
scheduled for processing, where each item belongs to a particular _kind_ (category).
Items of the same kind may be batched together into a _group_, and each group is
assigned to a single _facility_ on a single _day_ for processing.

The goal is to complete all items as close to their deadlines as possible while using
as few groups (and therefore as few facility bookings) as necessary.

This problem appeared in the **MiniZinc Challenge 2015**.

## Parameters

| Parameter        | Description                                                                     |
| ---------------- | ------------------------------------------------------------------------------- |
| `N`              | Total number of items to be scheduled                                           |
| `F`              | Number of available facilities                                                  |
| `MaxItemsPerDay` | Maximum number of items that may be processed on any single day                 |
| `MaxDay`         | The last day within the scheduling horizon                                      |
| `name`           | Human-readable name for each item                                               |
| `kind`           | The category (kind) of each item; only items of the same kind may share a group |
| `facility`       | The set of facilities that are capable of processing each item                  |
| `producedDay`    | The earliest day after which an item may be processed (it must be ready first)  |
| `deadLineDay`    | The preferred last day by which an item should be processed                     |

## Decision Variables

| Variable             | Description                                                                           |
| -------------------- | ------------------------------------------------------------------------------------- |
| `assignedGroup[i]`   | The group number that item `i` is assigned to                                         |
| `groupFacility[g]`   | The facility assigned to group `g` (0 if the group is unused)                         |
| `groupProcessDay[g]` | The day on which group `g` is processed (0 if unused)                                 |
| `itemProcessDay[i]`  | The day on which item `i` is processed (derived from its group's day)                 |
| `nGroups`            | The total number of distinct groups actually used                                     |
| `deadLinePenalty`    | The total number of days by which items exceed their deadlines, summed over all items |
| `objective`          | The combined objective value (see below)                                              |

## Constraints

- **Same-kind grouping**: Items may only share a group if they are of the same kind.
- **Facility compatibility**: The facility assigned to a group must be compatible with
  every item in that group.
- **Exclusive facility use**: A facility may only serve one group per day — two groups
  using the same facility must be scheduled on different days.
- **Availability window**: Each item must be processed _after_ its `producedDay`
  (i.e., it cannot be processed before it is ready).
- **Daily capacity**: No more than `MaxItemsPerDay` items may be processed across all
  groups on any single day.
- **Unused group marking**: Groups that contain no items are marked with a facility
  and day value of 0.

## Objective

The model **minimises** a weighted combination of two goals:

$$\text{objective} = 100 \times \texttt{deadLinePenalty} + \texttt{nGroups}$$

The large weight on `deadLinePenalty` means the primary goal is to process items on
or before their deadlines. Minimising `nGroups` is a secondary goal, encouraging the
solver to batch items into as few groups (facility bookings) as possible.

## Instance Naming Convention

Data file names follow the pattern `nNfFdDmMkK`, where:

- `N` = number of items
- `F` = number of facilities
- `D` = scheduling horizon (MaxDay)
- `M` = maximum items per day (MaxItemsPerDay)
- `K` = number of item kinds

## Notes

The origin of this specific problem formulation is not entirely clear. It resembles
industrial testing or quality-control scheduling scenarios where batches of products
must be tested using shared laboratory equipment within time windows. If you have
more context about the original application domain, please update this README.

## Model update summary

Added concise inline comments in gfd-schedule.mzn to clarify:

- item/group/facility variable roles,
- weighted objective semantics (`100 * deadLinePenalty + nGroups`),
- readability-only nature of the edits.
