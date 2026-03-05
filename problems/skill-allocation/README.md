# Skill Allocation Problem

The `skill_allocation_only.mzn` model assigns a set of service jobs to
engineers, possibly allowing training, while respecting various capacity and
location constraints.  It is designed for workforce planning scenarios.

## Inputs and parameters

- **Skills and engineers**
  - `sSkills`: list of all skill names; `SKILLS` is the index set.
  - `engineer_skills[e,s]` is 1 iff engineer `e` already has skill `s`.
  - `engineer_location[e]` gives a postcode (or 0) for each engineer.
  - `ENGS` is derived from `engineer_skills`.

- **Jobs**
  - `jobs[i,1]` is the skill required by job `i`.
  - Additional columns may encode geographical flags (interstate, overseas etc.).
  - `JOBS` is the set of job indices.

- **Training settings**
  - `nNewSkillsPerPerson`: how many new skills each engineer may learn.
  - `TRAINING` is the range `1..nNewSkillsPerPerson`.
  - `nTrainingCap` limits the total number of trainings (≤0 disables the cap).
  - `nInterstateCap`, `nOverseasCap` limit the number of jobs requiring travel.

- **Workload constraints**
  - `nMaxJobs` and `nMinJobs` bound the number of jobs assigned to each
    engineer (0 means the constraint is inactive).
  - `allEng` can be set to `true` to disable skill‑matching (any engineer may
    perform any job).

## Decision variables

- `allocations[i]` chooses an engineer for job `i`.
- `new_skills[e,t]` optionally assigns a new skill `t` to engineer `e` during
  planning; it must be a skill the engineer does **not** already have.
- `objective` counts the total number of trainings (the model aims to minimise
  this value, effectively preferring assignments that avoid training).

## Constraints

1. An engineer can only be allocated to a job if they already have the
   required skill or they receive training for that skill.
2. The total number of trainings must respect `nTrainingCap` if non‑negative.
3. The number of jobs per engineer must fall between `nMinJobs` and `nMaxJobs`
   if those bounds are positive.
4. Travel restrictions ensure no engineer exceeds interstate or overseas caps.

## Objective

Minimise `objective`, which is defined as the number of `new_skills` assigned;
this encourages matching existing skills before resorting to training.

To execute the model, supply a `.dzn` data file with the arrays described above.
Beginners can inspect the commented input lines near the top of the `.mzn` for
example data files.