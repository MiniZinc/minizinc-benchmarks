# On-Call Rostering

## Problem Description

This model solves an **on-call rostering** problem: given a pool of staff members and a rostering period (measured in days), assign exactly one staff member to be "on-call" for each day in the period.

The rostering period is divided into two types of days:

- **Weekdays** — Monday through Thursday, each treated as an individual slot.
- **Weekends** — Friday, Saturday and Sunday together count as a single on-call slot.

Staff members may have days on which they are **unavailable** (e.g. holidays, leave), and some may have days on which they are **required** to be on-call (pre-fixed shifts). The goal is to produce a fair, comfortable schedule while respecting all of these constraints.

---

## Parameters

| Parameter                | Description                                                                                                                                                                     |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `num_staff`              | Total number of staff members available for rostering.                                                                                                                          |
| `work_load`              | Each staff member's contracted workload as a percentage of full-time (1–100). Used to ensure fair distribution relative to contracted hours.                                    |
| `num_days`               | Total number of days in the rostering period (weekends count as one day each).                                                                                                  |
| `weekend_offset`         | Indicates which day of the first week is a weekend, so the model can correctly identify all weekend slots.                                                                      |
| `unavailable`            | For each staff member, the set of days on which they cannot be rostered on-call.                                                                                                |
| `fixed`                  | For each staff member, the set of days on which they must be rostered on-call (pre-assigned shifts).                                                                            |
| `adj_days_str`           | Relative weight (strength) of the penalty for rostering a staff member on consecutive days. Setting this to 0 disables the preference.                                          |
| `wed_before_weekend_str` | Relative weight of the penalty for rostering a staff member on the Wednesday immediately before a weekend they are also assigned to. Setting this to 0 disables the preference. |

---

## Decision Variables

| Variable                | Description                                                                                                                                                |
| ----------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `roster[d]`             | The staff member assigned to be on-call on day `d`. This is the primary output of the model.                                                               |
| `week_days_oc[s]`       | The total number of weekdays staff member `s` is rostered on-call.                                                                                         |
| `weekend_days_oc[s]`    | The total number of weekends staff member `s` is rostered on-call.                                                                                         |
| `week_day_bt`           | A balance tolerance variable: how much the weekday workload distribution is allowed to deviate from perfectly proportional (relative to contracted hours). |
| `weekend_bt`            | Same as above but for weekends.                                                                                                                            |
| `adj_days[i]`           | A penalty incurred when the same staff member is rostered on consecutive days `i` and `i+1`.                                                               |
| `wed_before_weekend[i]` | A penalty incurred when the same staff member is rostered on the Wednesday before weekend `i` and also on that weekend.                                    |
| `objective`             | The total penalty score to be minimised (sum of all individual penalties and balance tolerances).                                                          |

---

## Constraints

### Hard Constraints (must always hold)

- There must be at least two staff members and the roster must cover more than five days.
- There must not be any day on which every staff member is unavailable.
- A staff member's fixed (required) days cannot overlap with their unavailable days.
- No two staff members can both be fixed to the same day.
- Unavailability is strictly respected: a staff member is never rostered on a day they are unavailable.
- Pre-fixed assignments are enforced exactly.
- A staff member cannot be rostered on-call for **three or more consecutive days** (unless all those days are pre-fixed in the input).
- A staff member on-call over a weekend cannot also be on-call on the adjacent weekday immediately before or after that weekend (i.e. Thursday before or Monday after), unless those assignments are pre-fixed.
- A staff member cannot be on-call for two consecutive weekends, unless both are pre-fixed.

### Soft Constraints (penalised in the objective)

- **Workload balance**: The number of weekdays (and weekends) each staff member is on-call should be proportional to their contracted work load. Deviations are penalised via `week_day_bt` and `weekend_bt`.
- **Consecutive days**: Rostering the same staff member on back-to-back days is discouraged and penalised via `adj_days`.
- **Wednesday before weekend**: If a staff member is on-call over a weekend, they should ideally not also be on-call the Wednesday immediately preceding it. Violations are penalised via `wed_before_weekend`.

---

## Objective

The model **minimises** the `objective` variable, which is the sum of:

- All consecutive-day penalties (`adj_days`),
- All Wednesday-before-weekend penalties (`wed_before_weekend`),
- The weekday balance tolerance (`week_day_bt`),
- The weekend balance tolerance (`weekend_bt`).

A lower objective value means a more balanced and comfortable roster.

---

## Author

Model by **Julien Fischer** (Opturion Pty Ltd, <jfischer@opturion.com>).

> **Note:** No academic paper has been identified for this specific model. If you are aware of a published reference, please update this README.
