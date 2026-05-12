# GFD Schedule

## Problem Description

This model solves a **group-based facility scheduling** problem. A set of items must each be processed exactly once using a shared facility. Items are grouped before being sent to a facility, and an entire group is processed together on a single day by a single facility.

The scheduling decisions must respect:

- Each item has a **release day** (it cannot be processed before it is produced).
- Each item has a **deadline** (processing after the deadline incurs a penalty).
- Each item can only be processed at certain eligible facilities.
- All items within a group must share the same **kind** (items of different kinds cannot be placed in the same group).
- A facility can only handle one group per day.
- There is a global limit on the total number of items that can be processed on any single day.

The goal is to find an assignment of items to groups, a facility for each group, and a processing day for each group that minimises a weighted objective combining:

1. **Deadline penalty** — the total number of days by which items exceed their deadlines (weighted heavily), and
2. **Number of groups used** — minimising the number of groups reduces overall facility usage.

## Parameters

| Parameter        | Description                                                                           |
| ---------------- | ------------------------------------------------------------------------------------- |
| `N`              | Total number of items to be scheduled                                                 |
| `F`              | Total number of available facilities                                                  |
| `MaxItemsPerDay` | Maximum number of items that can be processed across all facilities on any single day |
| `MaxDay`         | The last day of the scheduling horizon                                                |
| `name`           | Human-readable name for each item                                                     |
| `kind`           | The type/category of each item (items of different kinds cannot share a group)        |
| `facility`       | The set of facilities that are eligible to process each item                          |
| `producedDay`    | The day after which each item becomes available for processing                        |
| `deadLineDay`    | The preferred deadline day for each item (processing after this day incurs a penalty) |

## Decision Variables

| Variable             | Description                                                                      |
| -------------------- | -------------------------------------------------------------------------------- |
| `assignedGroup[i]`   | The group number that item `i` is assigned to                                    |
| `groupFacility[g]`   | The facility assigned to group `g` (0 if the group is unused)                    |
| `groupProcessDay[g]` | The day on which group `g` is processed (0 if unused)                            |
| `itemProcessDay[i]`  | The day on which item `i` is processed (derived from its group's processing day) |
| `nGroups`            | The total number of distinct groups used                                         |
| `deadLinePenalty`    | The total accumulated lateness across all items that miss their deadline         |
| `objective`          | The combined objective value: `deadLinePenalty × 100 + nGroups`                  |

## Objective

The model **minimises** the `objective`, which is a weighted sum:

$$\text{objective} = 100 \times \text{deadLinePenalty} + \text{nGroups}$$

The large weight of 100 on the deadline penalty ensures that meeting deadlines is strongly preferred over reducing the number of groups. Subject to keeping penalties low, the model also tries to consolidate items into as few groups as possible, thereby reducing facility usage.

## Key Constraints

- **Same-kind grouping**: Only items of the same kind may share a group.
- **Group numbering**: Group indices are assigned in a structured, kind-based order to reduce symmetry in the search space.
- **Facility compatibility**: The facility chosen for a group must be eligible for every item in that group.
- **Exclusive facility use**: Each facility can process at most one group per day (enforced via a `cumulative` constraint).
- **Release dates**: Each item's group must be scheduled strictly after the item's `producedDay`.
- **Daily capacity**: The total number of items processed on any day must not exceed `MaxItemsPerDay`.
- **Deadline penalty**: Items processed after their `deadLineDay` contribute the excess days to the penalty.

## Notes

The origin of this specific problem instance set is not immediately clear from the model file. The name "gfd-schedule" may refer to an internal benchmark or an industrial application. If you have information about the original source, please update this README with an appropriate reference.

## Model update summary

Added concise inline comments in gfd-schedule2.mzn to clarify:

- item/group/facility variable roles,
- weighted objective semantics (`100 * deadLinePenalty + nGroups`),
- readability-only nature of the edits.
