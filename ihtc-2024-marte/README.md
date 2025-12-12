# Integrated Healthcare Timetabling

The model was developed to compete in the Integrated Healthcare Timetabling
Competition 2024 (https://ihtc2024.github.io/) and is released under the terms
of the MIT license (see LICENSE.txt).

The competition organizers provided 30 instances to the public for testing.
By enriching the original data slightly (for easier consumption by the MiniZinc
model), the instances in the folder public-instances/ were obtained.
These instances are released under the terms of the MIT license (see LICENSE.txt)
with kind permission of the competition organizers.

Contact: Michael Marte <informarte@freenet.de>

# Automatically generated description

## Overview

This MiniZinc model solves the **Integrated Healthcare Timetabling Problem**, as specified in the Integrated Healthcare Timetabling Competition (IHTC) 2024. The goal is to create an optimal schedule for hospital resources, including patient admissions, surgeries, room assignments, nurse allocations, and operating theatre usage, while respecting medical and operational constraints.

The model aims to minimise a weighted sum of penalties related to resource utilisation, patient care quality, and scheduling efficiency.

---

## Problem Description

Hospitals must manage multiple resources and constraints simultaneously:

- **Patients**: Each patient has attributes such as gender, age group, length of stay, surgery requirements, and mandatory/optional status.
- **Rooms**: Limited capacity, with restrictions on gender mixing and age group differences.
- **Operating Theatres (OTs)**: Limited daily availability for surgeries.
- **Surgeons**: Each surgeon has a maximum daily surgery time.
- **Nurses**: Assigned to rooms per shift, with skill levels and workload limits.
- **Scheduling Horizon**: A fixed number of days for mandatory patients; optional patients may be postponed.

The objective is to produce a feasible timetable that minimises penalties for violations and inefficiencies.

---

## Key Decision Variables

- `admission_days[p]`: Day on which patient _p_ is admitted.
- `room_assignments[p]`: Room assigned to patient _p_.
- `ot_assignments[p]`: Operating theatre assigned for patient _p_'s surgery.
- `nurse_assignments[r,d,s]`: Nurse assigned to room _r_ on day _d_ during shift _s_.

---

## Main Constraints

1. **H1 – No Gender Mix**: Patients of different genders cannot share a room on the same day.
2. **H2 – Room Compatibility**: Patients cannot be assigned to incompatible rooms.
3. **H3 – Surgeon Overtime**: Daily surgery time for each surgeon cannot exceed their limit.
4. **H4 – OT Overtime**: Total surgery time in an OT per day cannot exceed its capacity.
5. **H5 – Mandatory Patients**: All mandatory patients must be admitted within the scheduling period.
6. **H6 – Admission Window**: Patients admitted between release date and due date (optional patients can be postponed).
7. **H7 – Room Capacity**: Number of patients in a room per day cannot exceed its capacity.
8. **Nurse Assignment**: Nurses must be scheduled according to their availability and skill level.

---

## Objective

The model minimises a weighted sum of penalties:

- **Room Mixed Age**: Difference in age groups within a room.
- **Nurse Skill Level Deviation**: Assigning nurses below required skill level.
- **Continuity of Care**: Number of distinct nurses caring for a patient.
- **Excessive Nurse Workload**: Workload exceeding nurse capacity.
- **Opened Operating Theatres**: Number of OTs opened unnecessarily.
- **Surgeon Transfers**: Surgeons working in multiple OTs on the same day.
- **Patient Delay**: Delay between release date and admission.
- **Unscheduled Optional Patients**: Optional patients not admitted.

---

## Output

The model provides:

- Objective value and penalty breakdown.
- Resource utilisation metrics (nurse, room, surgeon, OT).
- JSON-formatted summary for easy integration with evaluation tools.

---

### References

- [Integrated Healthcare Timetabling Competition 2024](https://ihtc2024.github.io/)
- Based on healthcare scheduling research and optimisation techniques.
