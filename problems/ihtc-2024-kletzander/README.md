# Integrated Hospital Treatment and Care Scheduling (IHTC 2024)

This model was developed by Lucas Kletzander to compete in the
[Integrated Healthcare Timetabling Competition 2024 (IHTC 2024)](https://ihtc2024.github.io/).

## Overview

This model addresses a **hospital admission and surgery scheduling problem**. Given a set
of patients who need surgery and a planning horizon of several days, the model decides:

- **Which patients to admit** (some patients are optional, others are mandatory).
- **When to admit each patient** (which day within their allowed admission window).
- **Which room to assign each patient to**.
- **Which operating theatre (OT) to schedule each patient's surgery in**.

The goal is to admit as many patients as possible, as early as possible, while
satisfying all hard hospital constraints.

---

## Problem Description

A hospital has a fixed number of rooms, operating theatres, and surgeons. There are
already some **current occupants** (patients already in rooms at the start of the
planning horizon) whose presence must be considered. New patients arrive with various
requirements and restrictions.

Key challenges include:

- **Gender separation**: Patients of different genders cannot share a room during
  overlapping stays.
- **Room compatibility**: Some rooms are medically incompatible for certain patients
  (e.g., due to equipment or infection control).
- **Surgeon capacity**: Each surgeon has a daily limit on total surgery time.
- **OT capacity**: Each operating theatre has a daily limit on total surgery time.
- **Mandatory patients**: Certain patients _must_ be admitted; others are optional.
- **Admission windows**: Each patient has an earliest possible admission day
  (`release_day`) and a latest allowed admission day (`due_day`).
- **Room capacity**: The number of patients occupying a room at any point in time
  must not exceed that room's bed capacity. This is enforced using a
  `cumulative` constraint that accounts for both current occupants and newly
  admitted patients.

---

## Key Parameters

| Parameter                 | Description                                                    |
| ------------------------- | -------------------------------------------------------------- |
| `num_occupants`           | Number of patients already occupying rooms at the start        |
| `num_patients`            | Number of new patients to be scheduled                         |
| `horizon`                 | Number of days in the planning period                          |
| `num_rooms`               | Number of hospital rooms                                       |
| `num_ot`                  | Number of operating theatres                                   |
| `num_surgeons`            | Number of surgeons                                             |
| `oc_length_of_stay[c]`    | Remaining length of stay for current occupant `c`              |
| `oc_gender[c]`            | Gender of current occupant `c`                                 |
| `oc_room[c]`              | Room currently occupied by occupant `c`                        |
| `length_of_stay[p]`       | Length of stay required by patient `p`                         |
| `gender[p]`               | Gender of patient `p`                                          |
| `incompatible_rooms[p,i]` | Rooms that are incompatible for patient `p`                    |
| `mandatory[p]`            | Whether patient `p` must be admitted                           |
| `surgery_duration[p]`     | Duration of surgery for patient `p`                            |
| `surgeon[p]`              | Surgeon assigned to perform patient `p`'s surgery              |
| `release_day[p]`          | Earliest day patient `p` can be admitted                       |
| `due_day[p]`              | Latest day patient `p` can be admitted                         |
| `max_surgery[s,d]`        | Maximum total surgery time for surgeon `s` on day `d`          |
| `max_ot[o,d]`             | Maximum total surgery time in operating theatre `o` on day `d` |
| `capacity[r]`             | Bed capacity of room `r`                                       |
| `weight_selection`        | Penalty weight for each unscheduled optional patient           |
| `weight_delay`            | Penalty weight for each day of admission delay                 |

---

## Decision Variables

| Variable              | Description                                                                                                          |
| --------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `selection[p]`        | Boolean — whether patient `p` is admitted                                                                            |
| `admission[p]`        | Day on which patient `p` is admitted                                                                                 |
| `room[p]`             | Room assigned to patient `p`                                                                                         |
| `ot[p]`               | Operating theatre assigned for patient `p`'s surgery                                                                 |
| `admission_delay[p]`  | Number of days between the release day and actual admission day (0 if not selected)                                  |
| `room_admission[r,p]` | Auxiliary variable recording the admission day of patient `p` in room `r`, used to enforce capacity via `cumulative` |

---

## Constraints

The constraints are numbered following the IHTC 2024 problem specification:

1. **H1 – No Gender Mix**: Patients of different genders may not share a room during
   overlapping stays. This applies to both new patients and current occupants.
2. **H2 – Room Compatibility**: Patients cannot be placed in rooms listed as
   incompatible for them.
3. **H3 – Surgeon Overtime**: The total surgery time performed by each surgeon on any
   given day must not exceed their daily limit.
4. **H4 – OT Overtime**: The total surgery time scheduled in each operating theatre on
   any given day must not exceed its daily capacity.
5. **H5 – Mandatory Patients**: Every patient marked as mandatory must be admitted
   (i.e., `selection[p]` must be `true`).
6. **H6 – Admission Window**: Each patient must be admitted no later than their due day.
   The `admission_delay` is the gap between their release day and actual admission day.
7. **H7 – Room Capacity**: At any point during the planning horizon, the number of
   patients in a room must not exceed its capacity. This is modelled using a
   `cumulative` constraint over patient stay durations.

---

## Objective

The objective is to **minimise** the following weighted sum:

$$
\text{Objective} = \bigl(\text{unselected patients} \times w_{\text{selection}}\bigr)
+ \bigl(\sum_p \text{admission\_delay}[p] \times w_{\text{delay}}\bigr)
$$

where $w_{\text{selection}}$ (`weight_selection`) penalises each optional patient who
is not admitted, and $w_{\text{delay}}$ (`weight_delay`) penalises each day that an
admitted patient's admission is later than their release day.

This balances **throughput** (admitting more patients) against **timeliness**
(admitting them as promptly as possible).

---

## Notes

- This is a simplified version of the full IHTC 2024 problem: it does **not** include
  nurse scheduling, age group penalties, surgeon transfer penalties, or OT opening
  cost terms that appear in the full competition model.
- The `room_admission` auxiliary array is used to pass patient stay information to
  the `cumulative` global constraint for room capacity enforcement; its values are
  only meaningful for selected patients.

---

## References

- IHTC 2024 Competition: <https://ihtc2024.github.io/>
- Hindahl, K., Kletzander, L., Musliu, N. (2025). _A MiniZinc Model for the Integrated
  Healthcare Timetabling Competition 2024_. Proceedings of the MiniZinc Challenge 2025.
  _(Note: exact publication details are uncertain — please verify.)_

## Model update summary

Added concise inline comments in model4_opt.mzn to clarify:

- admission/room/OT decision variable roles,
- weighted objective composition (selection vs delay),
- readability-only intent of these updates.
