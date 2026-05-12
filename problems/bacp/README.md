# Balanced Academic Curriculum Problem (BACP)

## Problem Description

The **Balanced Academic Curriculum Problem (BACP)** involves scheduling a set of university courses across a fixed number of academic periods (e.g., semesters or terms). Each course must be assigned to exactly one period, subject to prerequisite relationships between courses and workload limits per period. The goal is to produce a schedule that is as **balanced as possible** — minimising the heaviest workload any single period places on students.

This is [CSPLib Problem 030](https://www.csplib.org/Problems/prob030/).

## Problem Inputs

| Parameter               | Description                                                               |
| ----------------------- | ------------------------------------------------------------------------- |
| `n_courses`             | Total number of courses in the curriculum                                 |
| `n_periods`             | Number of academic periods available                                      |
| `load_per_period_lb`    | Minimum total credit load allowed in any period                           |
| `load_per_period_ub`    | Maximum total credit load allowed in any period                           |
| `courses_per_period_lb` | Minimum number of courses that must be scheduled in any period            |
| `courses_per_period_ub` | Maximum number of courses that can be scheduled in any period             |
| `course_load`           | Array giving the number of academic credits each course carries           |
| `prerequisites`         | List of pairs `(a, b)` meaning course `b` must be taken before course `a` |

## Decision Variables

| Variable           | Description                                                                        |
| ------------------ | ---------------------------------------------------------------------------------- |
| `course_period[c]` | The period in which course `c` is scheduled                                        |
| `x[p, c]`          | Binary indicator: 1 if course `c` is assigned to period `p`, 0 otherwise           |
| `load[p]`          | The total credit load of period `p` (sum of credits of all courses in that period) |
| `objective`        | The maximum credit load across all periods — this is the value being minimised     |

## Constraints

1. **Assignment consistency**: The binary variable `x[p, c]` is 1 if and only if `course_period[c] = p`, linking the two representations together.
2. **Course count bounds**: Every period must contain at least `courses_per_period_lb` and at most `courses_per_period_ub` courses.
3. **Load bounds**: The total credit load of every period must be at least `load_per_period_lb` and at most `objective` (the current maximum load being minimised).
4. **Prerequisites**: If course `b` is a prerequisite of course `a`, then `b` must be scheduled in an earlier period than `a`.
5. **Redundant load constraints**: Additional constraints ensure that the remaining unscheduled courses (beyond any point in the schedule) can still satisfy the lower and upper load bounds. These help the solver reason more effectively but do not change the set of valid solutions.

## Objective

**Minimise** `objective`, which represents the **maximum total credit load across all periods**. By minimising this peak load, the schedule spreads student workload as evenly as possible across the curriculum.

## Reference

- Béjar, R., Manyà, F., Cabiscol, A., Fernández, C., & Gomes, C. (2003). _The Balanced Academic Curriculum Problem_. CSPLib Problem 030. https://www.csplib.org/Problems/prob030/

## Model update summary

Added concise inline comments in curriculum.mzn to clarify:

- assignment/load decision variable roles,
- objective variable meaning as peak period load,
- optimization direction (minimize maximum load).
