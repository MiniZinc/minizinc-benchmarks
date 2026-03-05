# Vaccine Trial Group Allocation Model

## **Overview**

This MiniZinc model addresses the problem of **allocating population groups to vaccine trials** in a way that maximises the overall information gained from the trials. The model considers demographic and health factors, exposure levels, and fairness constraints to ensure balanced and informative vaccine testing.

---

## **Problem Description**

The goal is to assign multiple population groups to one or more vaccines for clinical trials. Each group has attributes such as age, gender, health status, and exposure level. The allocation must satisfy constraints on group sizes, age distribution, gender balance, and shared vaccine participation, while maximising the minimum information value across all vaccines.

---

## **Inputs**

- **Sets and Enumerations:**

  - `VACCINE`: Available vaccines.
  - `AGE`: Age categories (e.g., BABY, CHILD, YOUTH, ADULT, SENIOR, AGED, ANCIENT).
  - `GENDER`: Gender categories (FEMALE, MALE, OTHER).
  - `HEALTH`: Health status (GOOD, POOR, COMPROMISED).
  - `EXPOSURE`: Exposure level (LOW, AVERAGE, HIGH, EXTREME).

- **Parameters:**
  - `m`: Number of population groups.
  - `age[g]`, `gender[g]`, `health[g]`, `exposure[g]`: Attributes of group `g`.
  - `size[g]`: Number of people in group `g`.
  - `minsize`: Minimum number of people per vaccine trial.
  - `age_group_min`, `age_group_max`: Minimum and maximum number of groups per age category for each vaccine.
  - `max_people_diff`: Maximum allowed difference in total participants across vaccines.
  - `max_share_vaccines`: Maximum number of vaccines shared by any two groups.
  - `health_information`, `exposure_information`: Information value weights based on health and exposure.

---

## **Decision Variables**

- `x[g]`: Set of vaccines assigned to group `g`.
- `vaccine_age[v,a]`: Number of groups of age `a` assigned to vaccine `v`.
- `total[v]`: Total number of participants assigned to vaccine `v`.
- `ngroups[gen,v]`: Number of groups of gender `gen` assigned to vaccine `v`.
- `information[v]`: Information value for vaccine `v`.
- `objective`: Minimum information value across all vaccines (to be maximised).

---

## **Constraints**

1. **Group Allocation Limits:**  
   Each group can participate in a limited number of vaccines based on its size.
2. **Age Distribution:**  
   Each vaccine must have a balanced number of groups from different age categories.
3. **Participant Balance:**  
   The difference in total participants across vaccines cannot exceed `max_people_diff`.
4. **Gender Balance:**  
   Each vaccine must have the same number of groups for each gender category.
5. **Shared Vaccines:**  
   Limit the number of vaccines shared between any two groups.
6. **Information Calculation:**  
   Information value depends on health and exposure diversity within the vaccine trial.

---

## **Objective**

Maximise:

```minizinc
objective = min(information);
```

This ensures that the least informative vaccine trial is as informative as possible, promoting fairness and diversity in data collection.

---

## **Applications**

- Clinical trial design for vaccines.
- Public health planning for diverse demographic representation.
- Optimisation of resource allocation in medical research.

---

## **References**

- Related to combinatorial optimisation in healthcare resource allocation.
- Inspired by principles of fairness and diversity in clinical trials.

---
