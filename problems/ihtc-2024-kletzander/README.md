# Integrated Hospital Treatment and Care Scheduling Model

## Overview

This MiniZinc model addresses a **hospital scheduling problem** that combines patient admission planning, room allocation, and operating theatre (OT) scheduling. The aim is to assign patients to rooms and schedule surgeries while respecting hospital constraints such as gender separation, room compatibility, resource limits, and mandatory patient requirements. The objective is to minimise a weighted sum of unselected patients and admission delays.

---

## Problem Description

Hospitals must manage:

- **Patient admissions** within a given planning horizon.
- **Room assignments** considering gender and compatibility restrictions.
- **Operating theatre scheduling** for surgeries, ensuring surgeon and OT capacity limits.
- **Mandatory patients** who must be admitted.
- **Room capacity constraints** based on length of stay and existing occupants.

The model seeks an optimal plan that satisfies these constraints and minimises penalties for delays and unselected patients.

---

## Key Sets and Parameters

- `num_occupants`: Current occupants in rooms.
- `num_patients`: Patients to be scheduled.
- `horizon`: Planning period in days.
- `num_rooms`: Available hospital rooms.
- `num_ot`: Number of operating theatres.
- `num_surgeons`: Number of surgeons.
- `max_incompatible`: Maximum incompatible room entries.

### Input Data

- `oc_length_of_stay[c]`: Length of stay for current occupant `c`.
- `oc_gender[c]`: Gender of occupant `c`.
- `oc_room[c]`: Room occupied by occupant `c`.
- `length_of_stay[p]`: Length of stay for patient `p`.
- `gender[p]`: Gender of patient `p`.
- `incompatible_rooms[p,i]`: Rooms incompatible for patient `p`.
- `mandatory[p]`: Whether patient `p` must be admitted.
- `surgery_duration[p]`: Duration of surgery for patient `p`.
- `surgeon[p]`: Surgeon assigned to patient `p`.
- `release_day[p]`: Earliest admission day for patient `p`.
- `due_day[p]`: Latest admission day for patient `p`.
- `max_surgery[s,d]`: Maximum surgery time for surgeon `s` on day `d`.
- `max_ot[o,d]`: Maximum OT time for theatre `o` on day `d`.
- `capacity[r]`: Capacity of room `r`.

---

## Decision Variables

- `selection[p]`: Boolean indicating if patient `p` is admitted.
- `admission[p]`: Admission day for patient `p`.
- `room[p]`: Room assigned to patient `p`.
- `ot[p]`: Operating theatre assigned to patient `p`.
- `admission_delay[p]`: Delay between release day and actual admission.
- `room_admission[r,p]`: Admission day for patient `p` in room `r`.

---

## Constraints

1. **Gender Separation**: No mixing of genders in the same room during overlapping stays.
2. **Room Compatibility**: Patients cannot be assigned to incompatible rooms.
3. **Surgeon and OT Capacity**: Daily surgery durations must not exceed limits.
4. **Mandatory Patients**: Must be admitted.
5. **Admission Window**: Patients admitted between release and due day.
6. **Room Capacity**: Enforced using cumulative constraints considering current occupants and new patients.

---

## Objective

Minimise:
\[
\text{Objective} = (\text{Number of unselected patients} \times \text{weight_selection}) + (\text{Sum of admission delays} \times \text{weight_delay})
\]

This balances admitting as many patients as possible and reducing delays.

---

## Notes

- This model is suitable for hospital resource planning and elective surgery scheduling.
- It integrates multiple constraints typical in healthcare operations research.
- Can be extended to include additional factors such as patient priority or emergency cases.
