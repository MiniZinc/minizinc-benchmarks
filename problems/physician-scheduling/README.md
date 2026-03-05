# Pandemic Physician Scheduling Instances for MiniZinc Challenge 2021:

The model is taken from the CPAIOR 2021 paper:
"Physician Scheduling During a Pandemic" from Tobias Geibinger, Lucas Kletzander, Matthias Krainz, Florian Mischek, Nysret Musliu and Felix Winter
https://link.springer.com/chapter/10.1007/978-3-030-78230-6_29

== Main Model File ==
physician-scheduling.mzn

Instances 1-8 are based on real-life instance 18, but are shrinked by taking a random subset of days and employees.
Instances 9-16 are based on instance 20, but are shrinked by taking a random subset of days and employees.
Instances 17 and 18 are a real-life instance.
Instances 19 and 20 are based on a real-life instances but have duplicated employees.

Contact:
lkletzan@dbai.tuwien.ac.at
tgeibing@dbai.tuwien.ac.at
fmischek@dbai.tuwien.ac.at
winter@dbai.tuwien.ac.at

# Automatically generated description

# Physician Scheduling Model

## **Overview**

This MiniZinc model addresses the **physician scheduling problem** in a hospital setting. The goal is to create an optimal schedule for medical personnel across multiple departments, stations, and shifts over a given planning period. The model considers staff preferences, skill requirements, risk factors, and operational constraints to ensure fair and efficient allocation of resources.

---

## **Problem Description**

- **Objective:** Assign physicians to shifts, stations, and skills for each day in the planning period while:
  - Meeting demand for each station, shift, and skill.
  - Respecting individual constraints such as maximum weekly hours, forbidden days, and risk levels.
  - Minimising an objective function that penalises undesirable assignments (e.g., station changes, high-risk personnel working, poor preference matches).

---

## **Key Inputs**

1. **Departments and Stations**

   - `numDepartments`: Number of hospital departments.
   - `departmentName`: Names of departments.
   - `numStations`: Number of stations (work locations).
   - `stationName`: Names of stations.
   - `stationDepartment`: Department associated with each station.
   - `stationCommon`: Indicates if a station is common/shared.

2. **Personnel Data**

   - `numPers`: Number of physicians.
   - `personName`: Names of physicians.
   - `numSkills`: Number of skills.
   - `skillName`: Names of skills.
   - `stationPrefs`: Preference weights for assigning personnel to stations and skills (0–3, 4 = forbidden).
   - `persRisk`: Indicates if a person has increased health risk.
   - `persRobustness`: Robustness score for personnel.
   - `persRequireWork`: Whether a person must work during this period.
   - `maxHoursWeek`: Maximum weekly working hours.
   - `forbiddenDays`: Days a person cannot work.
   - Historical data: consecutive workdays, last station worked, last shift worked.

3. **Shift Data**

   - `numShifts`: Number of shifts.
   - `numDays`: Number of days in the planning period.
   - `shiftName`: Names of shifts.
   - `shiftLength`: Length of each shift in hours.
   - `forbiddenSequences`: Disallowed shift sequences.
   - `demand`: Required number of staff per station, shift, day, and skill.

4. **Soft Constraint Weights**
   - `preferenceWeight`, `riskWeight`, `persWeight`, `stationWeight`: Penalty weights for objective calculation.

---

## **Decision Variables**

- `assignShift[i,j]`: Shift assigned to person `i` on day `j` (0 = day off).
- `assignStation[i,j]`: Station assigned to person `i` on day `j`.
- `assignSkill[i,j]`: Skill assigned to person `i` on day `j`.
- Helper variables:
  - `isWorking[i]`: Whether person `i` works at all.
  - `lastStation[i,j]`: Last station assigned to person `i` up to day `j`.
  - `stationChanges`: Total number of station changes.
  - `workingPers`: Number of working personnel.
  - `preferences`: Sum of preference penalties.
  - `workingRisk`: Weighted risk score.

---

## **Constraints**

- **Workload Limits:** Maximum consecutive workdays and weekly hours.
- **Demand Satisfaction:** Ensure required staff per station, shift, and skill.
- **Skill and Station Validity:** Assign only allowed combinations.
- **Forbidden Sequences:** Prevent disallowed shift patterns.
- **Personal Restrictions:** Honour forbidden days and risk considerations.
- **Station Change Tracking:** Minimise unnecessary station changes.
- **Department Consistency:** Limit number of departments per person.

---

## **Objective**

Minimise:

```
objective = workingPers \* persWeight
\+ preferences \* preferenceWeight
\+ workingRisk \* riskWeight
\+ stationChanges \* stationWeight;
```

This balances staffing efficiency, personnel preferences, risk management, and operational stability.

---

## **Output**

- Objective value and breakdown.
- Names of departments, stations, shifts, skills, and personnel.
- Assignment matrices for shifts, stations, and skills for each person and day.

---

## **References**

- Based on common hospital scheduling practices and constraint programming techniques.
- Related literature: N. Beldiceanu et al., "Global Constraints for Scheduling and Resource Allocation".

---
