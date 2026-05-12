# Physician Scheduling (MiniZinc Model)

## What problem is this model solving?

This model builds a **hospital physician schedule** over a planning horizon of `numDays` days.
For each person and each day, it decides:

- whether they work,
- which shift they work,
- which station (ward/unit) they work at,
- and which skill role they fill.

The schedule must satisfy staffing demand (by station, shift, day, and skill) while respecting work rules (hours, rest patterns, forbidden days, allowed skill/station combinations, etc.).

---

## Main decision variables

The core assignment variables are:

- `assignShift[p,d]` in `0..numShifts`: shift for person `p` on day `d` (`0` means off).
- `assignStation[p,d]` in `0..numStations`: station for person `p` on day `d`.
- `assignSkill[p,d]` in `0..numSkills`: skill role for person `p` on day `d`.

A consistency constraint ties these together so a day is either:

- fully off (`shift=0`, `station=0`, `skill=0`), or
- fully worked (all nonzero assignments).

Helpful derived variables include:

- `isWorking[p]`: whether person `p` works at least one day,
- `lastStation[p,d]`: last non-common station worked up to day `d`,
- `stationChanges`: total number of station changes,
- `workingPers`, `preferences`, `workingRisk`: objective components.

---

## Key constraints (beginner view)

The model enforces several groups of rules:

1. **Work pattern limits**
   - At most 6 consecutive working days.
   - Weekly total hours cannot exceed `maxHoursWeek[p]`.
   - Night-shift sequence restrictions are enforced using `indexNight` and previous-history data.

2. **Demand coverage**
   - Exact staffing demand must be met for each day/station/shift/skill.
   - There is special handling where one shift can subsume another on non-common stations.
   - Additional subsuming-demand rules apply by department/skill sets.

3. **Feasibility of assignments**
   - A person can only be assigned to station-skill combinations with preference value `< 4` (`4` means forbidden).
   - Forbidden shift sequences are disallowed (including transition from historical last shift).
   - Person-specific forbidden days must be off days.

4. **Operational continuity and policy**
   - Some reserve staff (`persRequireWork`) must be used.
   - Department switching is limited (modeled as max 2 distinct departments including history).
   - Station changes are tracked and penalized in the objective.

5. **Redundant/global counting constraints**
   - `global_cardinality_low_up` constraints tightly match daily totals for shifts, stations, and skills.
   - These strengthen consistency with demand totals.

---

## Objective

Yes—this is an **optimization** model.
It minimizes:

`objective = workingPers * persWeight + preferences * preferenceWeight + workingRisk * riskWeight + stationChanges * stationWeight`

Interpretation:

- fewer total workers used,
- better person–station–skill matches,
- fewer high-risk people assigned to higher-index departments,
- fewer station changes.

---

## Uncertainties and assumptions

A few parts are unclear from the model alone:

- `persRobustness` and `rbWeight` are declared but not used in the objective/constraints.
- A model comment says weekly hour logic assumes days start on Monday and `numDays` is divisible by 7.
- A comment notes a possible edge case in the night-sequence history handling.
- Department risk interpretation depends on how department indices are encoded in data (the model comments suggest departments are ordered by infection chance).

So this README describes the implemented logic, but some intended policy details likely depend on the original dataset and paper.

---

## References (identifiable)

- Model context appears to be from the physician scheduling benchmark used for MiniZinc Challenge 2021.
- Cited in repository material:
  - Geibinger, Kletzander, Krainz, Mischek, Musliu, Winter, **"Physician Scheduling During a Pandemic"**, CPAIOR 2021.
  - Link: https://link.springer.com/chapter/10.1007/978-3-030-78230-6_29
- MiniZinc library constraints/functions used directly in the model:
  - `nvalue` (via `nvalue_fn.mzn`),
  - `global_cardinality_low_up` (via `global_cardinality_low_up.mzn`).

## Model update summary

Added concise inline comments in physician-scheduling.mzn to clarify:

- shift/station/skill assignment decision variable roles,
- objective composition across staffing, preference, risk, and station changes,
- minimization intent for balanced roster quality.
