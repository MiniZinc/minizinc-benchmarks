# Rotating Workforce Scheduling Model

## **Overview**

This MiniZinc model solves the **Rotating Workforce Scheduling Problem**, which involves creating a fair and feasible work schedule for a set of employees over a planning horizon. The schedule must satisfy staffing requirements for different shifts while respecting labour regulations and fairness constraints.

The model is inspired by the paper _"The Rotating Workforce Scheduling Problem"_ by Nysret Musliu, Andreas Schutt, and Peter J. Stuckey, with some adjustments to reflect common rules used in Sweden.

---

## **Problem Description**

- **Goal:** Assign employees to shifts across multiple weeks so that:

  - Daily staffing requirements for each shift are met.
  - Employees receive adequate rest periods.
  - Night shifts and weekends are distributed fairly.
  - No employee works excessively without breaks.

- **Planning Horizon:**
  - `days = 7` (Monday to Sunday).
  - `weeks = employees` (each employee rotates weekly).
  - Shifts: `Day`, `Evening`, `Night`, plus `Off`.

---

## **Inputs**

- `int: employees`  
  Number of employees.
- `array[Days, Shifts] of int: requirements`  
  Minimum and maximum number of employees needed for each shift on each day.

---

## **Decision Variables**

- `array[Weeks, Days] of var ShiftsAndOff: schedule`  
  The main schedule matrix, where each entry is a shift or `Off`.
- `array[RepeatedWeeks, Days] of var ShiftsAndOff: repeated_schedule`  
  Extended schedule for applying constraints across week boundaries.

---

## **Key Constraints**

1. **Coverage Requirements:**  
   Each day must meet staffing requirements for all shifts:

   ```minizinc
   global_cardinality_low_up(schedule[.., day], set2array(S(Shifts)), requirements[day, ..], requirements[day, ..]);
   ```

2. **Rest Periods:**

   - At least **two consecutive days off** per week.
   - At most **five consecutive working days** without rest.

3. **Weekend Fairness:**  
   At least **one weekend off in every three-week period**.

4. **Night Shift Limit:**  
   No more than **two consecutive night shifts**, followed by a rest day.

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

This means the goal is to find **any feasible schedule** that satisfies all constraints.

---

## **Output**

The solution displays the schedule in a readable format:

- `D` for Day shift
- `E` for Evening shift
- `N` for Night shift
- `-` for Off day

---

## **Applications**

- Workforce planning in healthcare, manufacturing, and service industries.
- Ensuring compliance with labour laws and fairness in shift distribution.

---

## **References**

- Musliu, N., Schutt, A., & Stuckey, P. J. _The Rotating Workforce Scheduling Problem_.
- Related concepts: _Shift Scheduling_, _Fair Rostering_, _Constraint Programming for Workforce Management_.

---
