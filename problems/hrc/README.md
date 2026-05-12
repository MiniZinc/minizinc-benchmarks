# Hospital-Resident Problem with Couples (HRC)

## Problem Description

The **Hospital-Resident Problem with Couples (HRC)** is a variant of the classical stable matching problem. In the standard Hospital-Resident (HR) problem, individual residents are matched to hospitals based on mutual ranked preference lists, with the goal of finding a _stable_ matching — one where no unmatched resident-hospital pair would both prefer each other over their current assignments (such a pair is called a **blocking pair**).

HRC extends this setting by allowing some residents to participate as **couples**. A couple submits a _joint_ preference list of pairs of hospitals (one for each member), and must be assigned together — both members are placed at the hospitals in their chosen pair. This makes the problem significantly harder: unlike the individual case, a stable matching is not guaranteed to exist when couples are present.

This model addresses the problem of finding a matching that minimises the number of **unmatched residents**, subject to allowing exactly a specified number of blocking pairs. This is known as the _almost-stable_ HRC problem.

## Participants

- **Residents**: The pool of applicants. Residents are either _singles_ (independent applicants) or members of _couples_.
- **Couples**: Pairs of residents who must be assigned to hospitals together. Each couple submits a single joint ranked preference list of hospital pairs.
- **Singles**: Individual residents, each with their own ranked preference list of hospitals.
- **Hospitals**: Each hospital has a ranked preference list over individual residents and a maximum **capacity** (the number of residents it can accept).

## Input Parameters

| Parameter   | Description                                                                                                     |
| ----------- | --------------------------------------------------------------------------------------------------------------- |
| `nres`      | Total number of residents                                                                                       |
| `ncoup`     | Number of couples (occupying the first `2*ncoup` resident IDs)                                                  |
| `nhosp`     | Number of hospitals                                                                                             |
| `num_bp`    | Target number of blocking pairs allowed in the solution                                                         |
| `rpref`     | Preference lists for residents (for couples, each row encodes one hospital in a joint hospital-pair preference) |
| `rpref_len` | Length of each resident's preference list                                                                       |
| `hpref`     | Preference lists for hospitals (over individual residents)                                                      |
| `hpref_len` | Length of each hospital's preference list                                                                       |
| `hosp_cap`  | Capacity of each hospital                                                                                       |
| `hrank`     | For each hospital and resident, the rank the hospital assigns to that resident (0 if not ranked)                |

## Decision Variables

| Variable               | Description                                                                                                                |
| ---------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| `coup_pos[i]`          | The position in couple _i_'s joint preference list at which they are matched; set to one past the list end if unmatched    |
| `single_pos[i]`        | The position in single resident _i_'s preference list at which they are matched; set to one past the list end if unmatched |
| `coup_assigned[i,j]`   | `true` if couple _i_ is matched to the hospital pair at position _j_ of their preference list                              |
| `single_assigned[i,j]` | `true` if single resident _i_ is matched to the hospital at position _j_ of their preference list                          |
| `hosp_assigned[i,j]`   | `true` if hospital _i_ has its _j_-th ranked resident assigned to it                                                       |
| `coup_unassigned[i]`   | `true` if couple _i_ is not matched to any hospital pair                                                                   |
| `single_unassigned[i]` | `true` if single resident _i_ is not matched to any hospital                                                               |
| `coup_bp[i,j]`         | `true` if couple _i_ and the hospital pair at position _j_ form a blocking pair                                            |
| `single_bp[i,j]`       | `true` if single resident _i_ and the hospital at position _j_ form a blocking pair                                        |

## Constraints

1. **Preference list channeling**: Each resident (single or couple) is assigned to exactly one position on their preference list, or is left unmatched.
2. **Consistency**: Resident assignments and hospital assignments are mutually consistent — if a resident is assigned to a hospital, that hospital also records the assignment.
3. **Capacity**: No hospital is assigned more residents than its capacity.
4. **Blocking pair counting**: The total number of blocking pairs across all singles and couples equals exactly `num_bp`.
5. **Blocking pair definitions**: Four types of blocking pairs are modelled (Types 1, 2a/2b, 3a, 3bcd), covering all combinations where a resident (or couple) and hospital(s) would mutually prefer each other, accounting for the special case where both members of a couple apply to the same hospital.

## Objective

Minimise the total number of **unmatched residents**:

$$\text{objective} = 2 \times |\{\text{unmatched couples}\}| + |\{\text{unmatched singles}\}|$$

Couples are counted as 2 since each couple represents two residents. A solution with `num_bp = 0` corresponds to a fully stable matching (if one exists); increasing `num_bp` relaxes stability in exchange for fewer unmatched residents.

## References

This model relates to the study of _almost-stable_ matchings in the HRC setting:

- Manlove, D. F., McBride, I., & Trimble, J. (2017). "Almost-stable matchings in the Hospitals/Residents problem with Couples." _Theoretical Computer Science_, 669, 12–21. https://doi.org/10.1016/j.tcs.2017.01.005
- Manlove, D. F. (2013). _Algorithmics of Matching Under Preferences_. World Scientific. (Chapter on HRC.)

> **Note**: The exact data instances and the specific classification of blocking pair types (Types 1, 2a/2b, 3a, 3bcd) used in this model closely follow the framework in Manlove et al. (2017), but this has not been independently verified against the paper. An expert familiar with that work should confirm the correspondence.

## Model update summary

Added concise inline comments in hrc.mzn to clarify:

- single/couple assignment channeling variables,
- objective semantics as unmatched-resident count,
- weighting of unmatched couples as two residents.
