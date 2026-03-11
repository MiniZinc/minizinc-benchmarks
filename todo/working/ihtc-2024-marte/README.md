# Integrated Healthcare Timetabling (IHTC 2024)

## Problem Description

This model addresses the **Integrated Healthcare Timetabling** problem, as defined for the [International Nurse Rostering Competition / Integrated Healthcare Timetabling Competition 2024 (IHTC 2024)](https://ihtc2024.github.io/). The problem combines several interrelated hospital scheduling decisions into a single optimisation problem:

- **When** should each patient be admitted for surgery?
- **Which room** should each patient stay in?
- **Which operating theater** should each patient's surgery take place in?
- **Which nurse** should be assigned to care for each room on each shift?

The goal is to satisfy all hard requirements (e.g. room capacity, surgeon availability) while minimising a weighted sum of soft-constraint violations (e.g. mixed age groups in rooms, nurse workload excess).

This model was developed by Michael Marte to compete in IHTC 2024 and is released under the MIT licence.

## Entities

| Entity                       | Description                                                                                                                                                                                                                                                                                                                                |
| ---------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **Patients**                 | People requiring surgery and a hospital stay. May be _mandatory_ (must be admitted in the current period) or _optional_ (can be postponed). Each patient has a release date, an optional due date, a surgery duration, a required surgeon, a list of incompatible rooms, and daily workload and skill-level requirements for nursing care. |
| **Occupants**                | Patients already in the hospital at the start of the scheduling period. Their room assignments and stay lengths are fixed; they still contribute to room capacity, nurse workload, and skill requirements.                                                                                                                                 |
| **Surgeons**                 | Each surgeon has a maximum amount of surgery time available per day.                                                                                                                                                                                                                                                                       |
| **Operating Theaters (OTs)** | Each OT has a daily availability limit (total surgery minutes it can host per day).                                                                                                                                                                                                                                                        |
| **Rooms**                    | Hospital rooms with fixed bed capacity.                                                                                                                                                                                                                                                                                                    |
| **Nurses**                   | Each nurse has a skill level and a roster of shifts they work, each with a maximum workload capacity.                                                                                                                                                                                                                                      |

## Decision Variables

| Variable                     | Meaning                                                           |
| ---------------------------- | ----------------------------------------------------------------- |
| `admission_days[p]`          | The day on which patient `p` is admitted for surgery.             |
| `room_assignments[p]`        | The room assigned to patient `p` for their stay.                  |
| `ot_assignments[p]`          | The operating theater in which patient `p`'s surgery takes place. |
| `nurse_assignments[r, d, s]` | The nurse assigned to room `r` on day `d` during shift `s`.       |

## Hard Constraints

These must be satisfied in any feasible solution:

| ID     | Constraint                                                                                                                                                                                     |
| ------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **H1** | **No gender mix** — patients of different genders may not share a room on the same day.                                                                                                        |
| **H2** | **Compatible rooms** — each patient may only be placed in one of their compatible rooms (some rooms are explicitly incompatible per patient).                                                  |
| **H3** | **Surgeon overtime** — the total surgery time assigned to a surgeon on any given day must not exceed their daily limit.                                                                        |
| **H4** | **OT overtime** — the total surgery time in any operating theater on any day must not exceed its available capacity.                                                                           |
| **H5** | **Mandatory admission window** — all mandatory patients must be admitted within the scheduling period, on a day between their release date and due date.                                       |
| **H6** | **Admission day bounds** — optional patients may be admitted from their release date onwards (with no upper bound; if admitted outside the planning period they are considered "unscheduled"). |
| **H7** | **Room capacity** — the number of patients (occupants + admitted patients) in a room on any day must not exceed its bed capacity.                                                              |

Each room must also be assigned exactly one nurse per shift on every day of the scheduling period, chosen from nurses who are rostered to work that shift.

## Soft Constraints and Objective

The objective is to **minimise** a weighted sum of the following penalty terms:

| ID     | Penalty                    | Description                                                                                                                                               |
| ------ | -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **S1** | `room_mixed_age`           | For each room and day, the difference between the highest and lowest age group present. Mixing very different age groups is undesirable.                  |
| **S2** | `room_nurse_skill`         | If the nurse assigned to a room has a lower skill level than a patient requires, the shortfall (summed over all patients, shifts, and days) is penalised. |
| **S3** | `continuity_of_care`       | The total number of _distinct_ nurses who care for each patient across their entire stay. Fewer different nurses means better continuity of care.         |
| **S4** | `nurse_eccessive_workload` | The amount by which each nurse's workload exceeds their shift capacity (summed over all nurses and shifts).                                               |
| **S5** | `open_operating_theater`   | The number of operating theaters that are opened (used) on each day. Fewer open OTs reduces overhead.                                                     |
| **S6** | `surgeon_transfer`         | The number of different OTs a surgeon uses on a given working day (above one). Moving between OTs within a day is inefficient.                            |
| **S7** | `patient_delay`            | For each patient, the number of days between their release date and their actual admission date. Earlier admission is better.                             |
| **S8** | `unscheduled_optional`     | The number of optional patients who are not admitted within the current scheduling period.                                                                |

Each penalty is multiplied by a problem-instance-specific weight before being summed into the overall objective.

## Reference

The problem specification was defined by the IHTC 2024 competition organisers. For full details, see:

> **Integrated Healthcare Timetabling Competition 2024**  
> https://ihtc2024.github.io/

This MiniZinc model was written by **Michael Marte** (`informarte@freenet.de`) and subsequently modified by the MiniZinc Challenge Organisers to allow running under finite-domain (FD) solvers.
