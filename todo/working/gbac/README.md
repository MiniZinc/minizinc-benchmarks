# Generalised Balanced Academic Curriculum (GBAC)

## Problem Description

The **Generalised Balanced Academic Curriculum Problem (GBAC)** is an academic scheduling problem where a set of courses must be assigned to study periods (e.g., semesters or terms). The goal is to produce a timetable that respects prerequisite relationships between courses, keeps the number of courses per period within acceptable limits, balances the study workload evenly across all periods, and avoids placing courses in periods that are deemed undesirable.

This is **Problem 64** in [CSPLib](http://www.csplib.org/Problems/prob064/). Further details and benchmark instances are available at the [GBAC project page](http://satt.diegm.uniud.it/projects/gbac/).

## Problem Parameters

| Parameter                     | Meaning                                                                      |
| ----------------------------- | ---------------------------------------------------------------------------- |
| `n_courses`                   | Total number of courses                                                      |
| `n_periods`                   | Total number of study periods                                                |
| `n_curricula`                 | Number of degree programmes (curricula)                                      |
| `courses_of`                  | For each curriculum, the set of courses belonging to it                      |
| `n_precedences`               | Number of prerequisite relationships                                         |
| `precedes`                    | Each row gives a pair (A, B) meaning course A must be taken before course B  |
| `min_courses` / `max_courses` | Minimum and maximum number of courses allowed per period within a curriculum |
| `course_load`                 | The workload (credit hours or similar) associated with each course           |
| `n_undesirables`              | Number of course–period combinations that are considered undesirable         |
| `undesirable`                 | Each row gives a pair (course, period) that should be avoided                |
| `w1`                          | Weight applied to the load-balance penalty in the objective                  |
| `w2`                          | Weight applied to the undesirable-assignment penalty in the objective        |

## Decision Variables

| Variable         | Meaning                                                                                    |
| ---------------- | ------------------------------------------------------------------------------------------ |
| `period_of[c]`   | The period to which course `c` is assigned — this is the primary decision variable         |
| `load_of[cu, p]` | The total course load assigned to curriculum `cu` in period `p`                            |
| `delta[cu, p]`   | The deviation of the load in period `p` for curriculum `cu` from the ideal (balanced) load |

## Constraints

1. **Cardinality per period**: For every curriculum, each period must contain between `min_courses` and `max_courses` of that curriculum's courses. This prevents periods from being over- or under-loaded in terms of course count.

2. **Prerequisites**: If course A is a prerequisite for course B, then A must be scheduled in an earlier period than B.

3. **Load tracking**: For each curriculum and period, the total workload is computed by summing the `course_load` of every course from that curriculum assigned to that period.

4. **Load balance deviation**: For each curriculum and period, `delta` measures how far the actual load deviates from the ideal (perfectly even) load. The ideal load is the curriculum's total workload divided evenly across all periods; because this may not be a whole number, both a floor and a ceiling of the ideal are computed, and `delta` is zero when the actual load falls within that range.

## Objective

Minimise a weighted sum of two penalties:

$$\text{objective} = w_1 \cdot \sum_{c,p} \delta[c,p]^2 \;\;+\;\; w_2 \cdot \text{undesirable\_violation}$$

- **Load imbalance** ($w_1$ term): The sum of _squared_ deviations from the ideal load, across all curricula and periods. Using the squared error penalises large imbalances more heavily and allows direct comparison with results reported in the literature (see Bettinelli et al., 2008).
- **Undesirable violations** ($w_2$ term): The count of courses that have been placed in a period marked as undesirable for that course.

A lower objective value is better; zero would mean a perfectly balanced schedule with no undesirable placements.

## Reference

Bettinelli, A., Cacchiani, V., Roberti, R., & Toth, P. (2008). _An Overview of Curriculum-Based Course Timetabling_. Presented at CPAIOR 2008. DOI: [10.1007/978-3-540-88439-2_11](http://dx.doi.org/10.1007/978-3-540-88439-2_11)

Model originally by Jean-Noel Monette, modified by Gustav Bjordal, with contributions from Fatima Zohra Lebbah, Justin Pearson, and Pierre Flener.
