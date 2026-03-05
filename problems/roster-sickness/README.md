# MiniZinc Model: Employee Roster Adjustment with Sickness Constraints

## **Overview**

This MiniZinc model addresses the **employee shift scheduling problem** under sickness constraints. The goal is to adjust an existing roster when some employees are unavailable due to sickness, while maintaining fairness and operational requirements. The model ensures that previously assigned shifts are respected where possible and that new assignments comply with expertise and overlap rules.

---

## **Problem Description**

- **Scenario:** A set of employees is scheduled to work across multiple shifts. Some employees become unavailable (sick), and the roster must be updated.
- **Goal:** Reassign shifts to available employees while:
  - Preserving existing assignments where possible.
  - Avoiding overlapping shifts for any employee.
  - Ensuring employees have the required expertise for their assigned shifts.
  - Minimising deviation from contractual working hours.
  - Maximising the number of assigned shifts.

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
- `array[EMPLOYEE, SHIFT] of bool: is_assigned`  
  Indicates if an employee was originally assigned to a shift.
- `int: time_units_per_hour`  
  Conversion factor for time units.

Derived sets:

- `SHIFT = 1..n_shifts`
- `EMPLOYEE = 1..n_employees`
- `EXPERTISE = 1..n_expertises`

---

## **Decision Variables**

- `array[EMPLOYEE, SHIFT] of var bool: assigned`  
  Indicates whether an employee is assigned to a shift after adjustment.
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

1. **Preserve Existing Assignments:**  
   If an employee was assigned and is still available, keep the assignment.
2. **No Double Assignments:**  
   Each shift can have at most one employee.
3. **No Overlapping Shifts:**  
   Employees cannot work two overlapping shifts.
4. **Expertise Requirement:**  
   Employees can only be assigned to shifts requiring their expertise.
5. **Respect Original Assignments:**  
   If another employee was originally assigned to a shift, prevent reassignment unless necessary.

---

## **Objective**

Maximise:

```minizinc
objective = W * number_assigned_shifts - summed_abs_contract_diff;
```

Where `W` is a weight factor ensuring the primary goal is to maximise assigned shifts while minimising contract deviations.

---

## **Output**

- Number of assigned shifts.
- Sum of absolute contract deviations.
- Objective value.

---

## **Applications**

- Workforce scheduling in healthcare, retail, or manufacturing.
- Dynamic roster adjustment under unexpected absences (e.g., sickness).

---
