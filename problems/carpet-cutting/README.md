# Carpet Cutting

## Problem Description

The **Carpet Cutting** problem is a two-dimensional cutting and packing problem. The goal is to cut all required carpet pieces from a single rectangular **carpet roll** of fixed width and variable length, arranging every piece so that none of them overlap and the total roll length used is as small as possible (minimising waste).

Two distinct types of carpet pieces must be accommodated:

- **Room carpets** — irregular (rectilinear) shapes made up of one or more non-overlapping rectangles. Think of an L-shaped or T-shaped room floor plan. Each room carpet may optionally be rotated by 90°, 180°, or 270° before it is placed on the roll.
- **Stair carpets** — simple rectangles that cover a flight of stairs. Because the joins between pieces can be hidden under the stair nosing (where the tread meets the riser), a stair carpet is allowed to be cut into several strips and placed separately, subject to constraints on how many cuts are permitted and how many steps each strip must cover.

The carpet roll has a **fixed width** (`roll_wid`) and the solver determines the minimum required **length** (`objective`), which is the quantity being minimised.

---

## Parameters

### Carpet Roll

| Parameter      | Meaning                        |
| -------------- | ------------------------------ |
| `roll_wid`     | Fixed width of the carpet roll |
| `max_roll_len` | Upper bound on the roll length |

### Room Carpets

| Parameter                              | Meaning                                                                                                   |
| -------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| `n_rm`                                 | Number of room carpets                                                                                    |
| `rm_rec_ids[i]`                        | Set of rectangle IDs that together make up room carpet _i_                                                |
| `rm_ori[i]`                            | Allowed orientations (subset of {0°, 90°, 180°, 270°}) for room carpet _i_                                |
| `rm_max_len[i]`, `rm_max_wid[i]`       | Bounding-box dimensions of room carpet _i_ in its default (0°) orientation                                |
| `rm_rec_len[j]`, `rm_rec_wid[j]`       | Dimensions of individual rectangle _j_ in its default orientation                                         |
| `rm_rec_os_x[j,o]`, `rm_rec_os_y[j,o]` | Position offset of rectangle _j_ relative to the origin of its room carpet when placed in orientation _o_ |

### Stair Carpets

| Parameter                | Meaning                                                                                                                                |
| ------------------------ | -------------------------------------------------------------------------------------------------------------------------------------- |
| `n_st`                   | Number of stair carpets                                                                                                                |
| `st_len[i]`, `st_wid[i]` | Dimensions of stair carpet _i_                                                                                                         |
| `st_no_steps[i]`         | Number of steps that stair carpet _i_ covers (also the number of equal-width sub-rectangles it is divided into for placement purposes) |
| `st_min_steps[i]`        | Minimum number of steps that must appear in each cut segment                                                                           |
| `st_max_breaks[i]`       | Maximum number of cuts allowed for stair carpet _i_                                                                                    |

---

## Decision Variables

| Variable                           | Meaning                                                                                              |
| ---------------------------------- | ---------------------------------------------------------------------------------------------------- |
| `objective`                        | The roll length used — the value being minimised                                                     |
| `rm_x[i]`, `rm_y[i]`               | Position of the origin of room carpet _i_ on the roll (along the length and width axes respectively) |
| `rm_vori[i]`                       | Chosen orientation (1–4) of room carpet _i_                                                          |
| `rm_rec_x[j]`, `rm_rec_y[j]`       | Absolute position of rectangle _j_ (a sub-rectangle of a room carpet) on the roll                    |
| `rm_rec_vlen[j]`, `rm_rec_vwid[j]` | Effective (post-rotation) dimensions of room carpet rectangle _j_                                    |
| `st_rec_x[j]`, `st_rec_y[j]`       | Position of step-rectangle _j_ (a sub-rectangle of a stair carpet) on the roll                       |

---

## Constraints

1. **Roll boundary** — every carpet piece (both room and stair) must fit entirely within the roll's width and within the chosen roll length.
2. **Orientation** — each room carpet is placed in one of its permitted orientations; the two boolean helpers `rm_ori_0_or_180` and `rm_ori_0_or_90` together encode which of the four orientations is selected and drive the dimension-swapping logic.
3. **Offset consistency** — each rectangle of a room carpet is placed at a position determined by the room carpet's origin plus the appropriate orientation-dependent offset.
4. **Stair partition constraints** — consecutive step-rectangles of the same stair carpet must follow the ordering rules (symmetry breaking), each segment must span at least `st_min_steps` steps, and the total number of cuts must not exceed `st_max_breaks`.
5. **Cumulative constraints** — applied along both axes to provide resource-level reasoning about how the roll width and length are consumed.
6. **Non-overlap** — the global `diffn` constraint ensures that no two rectangles (whether from room or stair carpets) overlap on the roll.

---

## Objective

Minimise `objective` — the total length of carpet roll consumed.

---

## References

This problem appears to originate from industrial carpet-laying applications and has been used as a benchmark in the context of the **MiniZinc Challenge**. A closely related formulation is described in:

> Simonis, H., & O'Sullivan, B. (2011). _Almost square packing_. In _Proceedings of the 8th International Conference on Integration of AI and OR Techniques in Constraint Programming (CPAIOR 2011)_, Lecture Notes in Computer Science, vol. 6697. Springer.

> Belov, G., Kartak, V., Rohling, H., & Scheithauer, G. (2010). _One-dimensional relaxations and LP bounds for orthogonal packing_. _International Transactions in Operational Research_, 16(6), 745–766.

_(Note: the exact provenance of this specific carpet-cutting formulation has not been confirmed. If you know the original source, please update this section.)_
