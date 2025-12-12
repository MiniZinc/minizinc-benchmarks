# MiniZinc Model: Employee Shift Scheduling

## **Overview**

This MiniZinc model solves a **shift scheduling problem** for employees. The goal is to assign employees to shifts while respecting contractual limits, expertise requirements, and avoiding overlapping assignments. The model aims to maximise the number of assigned shifts while keeping the workload close to each employee's contract hours.

---

## **Problem Description**

- **Goal:** Assign employees to shifts such that:
  - No employee works overlapping shifts.
  - Employees only work shifts for which they have the required expertise.
  - Workload does not exceed 130% of the employee's contract hours.
  - Maximise the number of assigned shifts while minimising deviation from contract hours.

---

## **Parameters**

- `int: n_shifts`  
  Total number of shifts.
- `int: n_employees`  
  Total number of employees.
- `int: n_expertises`  
  Number of expertise types.
- `array[EMPLOYEE] of int: contract`  
  Contracted hours for each employee.
- `array[EMPLOYEE] of set of EXPERTISE: employee_expertises`  
  Expertise areas for each employee.
- `array[SHIFT] of EXPERTISE: req_expertise`  
  Required expertise for each shift.
- `array[SHIFT] of int: start_time, stop_time`  
  Start and end times for each shift.
- `int: time_units_per_hour`  
  Conversion factor for time units.

Derived sets:

- `set of int: SHIFT = 1..n_shifts`
- `set of int: EMPLOYEE = 1..n_employees`
- `set of int: EXPERTISE = 1..n_expertises`

---

## **Decision Variables**

- `array[EMPLOYEE, SHIFT] of var bool: assigned`  
  Indicates whether an employee is assigned to a shift.
- `array[EMPLOYEE] of var int: contract_diff`  
  Difference between actual worked time and contract hours.
- `var int: number_assigned_shifts`  
  Total number of assigned shifts.
- `var int: summed_abs_contract_diff`  
  Sum of absolute deviations from contract hours.
- `var int: objective`  
  Weighted objective combining assigned shifts and contract deviation.

---

## **Constraints**

1. **No Double Assignments:**  
   Each shift can have at most one employee:

   ```minizinc
   sum(e in EMPLOYEE)(assigned[e, s]) <= 1;
   ```

2. **No Overlapping Shifts:**  
   Employees cannot work two shifts that overlap:

   ```minizinc
   assigned[e, s1] + assigned[e, s2] <= 1;
   ```

3. **Expertise Requirement:**  
   Employees can only be assigned to shifts requiring their expertise:

   ```minizinc
   not assigned[e, s] if req_expertise[s] not in employee_expertises[e];
   ```

4. **Contract Limit:**  
   Total worked time cannot exceed 130% of contract hours:
   ```minizinc
   10 * worked_time <= 13 * contract[e];
   ```

---

## **Objective**

Maximise:

```minizinc
objective = W * number_assigned_shifts - summed_abs_contract_diff;
```

Where `W` is a weight factor ensuring the primary goal is to maximise assigned shifts.

---

## **Output**

- Number of assigned shifts.
- Sum of absolute contract deviations.
- Objective value.

---

## **Applications**

- Workforce scheduling in healthcare, retail, or manufacturing.
- Optimising staff allocation while respecting labour agreements.

---
