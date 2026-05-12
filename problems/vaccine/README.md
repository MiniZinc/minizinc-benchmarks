# Vaccine Trial Assignment (MiniZinc Model)

## What problem is this model solving?
This model designs how population groups are assigned to multiple candidate vaccines in a trial.

Each group has attributes (age, gender, health status, exposure risk, and group size), and can be tested on one or more vaccines. The goal is to build a trial plan that is:
- feasible (respects capacity and policy limits),
- balanced (across age, gender, and total participants), and
- informative (collects strong information for each vaccine).

In short: **choose who gets tested on which vaccines so every vaccine gets a fair and useful trial population**.

## Main inputs (data)
The data file provides:
- `VACCINE`: set of vaccines under study.
- `GROUP = 1..m`: population groups.
- Group features: `age[g]`, `gender[g]`, `health[g]`, `exposure[g]`, `size[g]`.
- Policy/feasibility limits:
  - `minsize`: minimum people needed per group-vaccine test.
  - `age_group_min[a]`, `age_group_max[a]`: min/max number of groups of each age per vaccine.
  - `max_people_diff`: allowed difference in total tested people between any two vaccines.
  - `max_share_vaccines`: max number of vaccines shared by any pair of groups.
- Information weights:
  - `health_information[h]`
  - `exposure_information[e]`

## Decision variables
- `x[g]` (set of vaccines): vaccines assigned to group `g`.
  - If `v in x[g]`, group `g` participates in vaccine `v`.
- Derived helper variables used for reporting/checking:
  - `total[v]`: estimated number of participants for vaccine `v`.
  - `ngroups[gen,v]`: number of groups of gender `gen` in vaccine `v`.
  - `vaccine_age[v,a]`: number of age-`a` groups in vaccine `v`.
  - `information[v]`: information score gathered for vaccine `v`.

## Core constraints (plain language)
1. **Per-group capacity**  
   A group cannot be assigned to too many vaccines:  
   `card(x[g]) <= size[g] div minsize`.

2. **Age composition per vaccine**  
   For each vaccine, the count of assigned groups in each age class must stay within `age_group_min..age_group_max`.

3. **Participant-balance across vaccines**  
   Total participants per vaccine must be close: for every pair `(v1, v2)`,  
   `|total[v1] - total[v2]| <= max_people_diff`.

4. **Gender balance across vaccines**  
   For each gender, each vaccine must have the same number of groups.

5. **Overlap control between groups**  
   Any two groups may share at most `max_share_vaccines` vaccines.

## Objective
The model computes `information[v]` for each vaccine and then maximizes:
- `objective = min(information)`

So it is a **max–min objective**: improve the *worst* information score among all vaccines, making the trial robustly informative rather than optimizing only the best vaccine.

## About uncertainty / modeling assumptions
This is a planning model under uncertainty in real-world outcomes. It does **not** simulate biological efficacy directly; instead it uses proxy information scores (`health_information × exposure_information`).

An optional extension (`extension = true`) reduces incremental value when a vaccine already includes another group with the same `(health, exposure)` profile. This encodes diminishing returns from repeated similar profiles.

Because of these assumptions, solution quality depends strongly on how well the input weights and bounds reflect real trial goals.

## Notes
- The model includes symmetry-breaking (`lex_lesseq`) and a search annotation (`int_search(...)`) to speed solving.
- Outputs print assignment matrices and summary counts (`x`, `vaccine_age`, `ngroups`, `total`, `information`).

## References / identifiable building blocks
- MiniZinc global constraint: `global_cardinality_low_up.mzn`
- MiniZinc symmetry utility: `lex_lesseq.mzn`
- General MiniZinc documentation: https://docs.minizinc.dev/

## Model update summary

Added concise inline comments in vaccine.mzn to clarify:

- vaccine-assignment and trial-information decision variable semantics,
- feasibility constraints for group capacity, balance, and overlap,
- objective intent as maximizing the weakest vaccine information score.