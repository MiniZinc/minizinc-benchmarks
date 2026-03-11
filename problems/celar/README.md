# CELAR Radio Link Frequency Assignment Problem

## Problem Description

This model addresses the **Radio Link Frequency Assignment Problem (RLFAP)**, a real-world combinatorial optimisation problem originating from military telecommunications. The goal is to assign a radio frequency to each communication link in a network so that interference between links is minimised or eliminated.

Each communication link is assigned a frequency drawn from a permitted set. Two links that share or are close to the same frequency can interfere with one another. To avoid this, two types of constraint are imposed on pairs of links:

1. **Hard equality constraints** — the absolute difference between the two assigned frequencies must equal exactly a given value $k'$: $|f_i - f_j| = k'$.
2. **Soft inequality constraints** — the absolute difference between the two assigned frequencies should be _greater than_ a given value $k$: $|f_i - f_j| > k$. If no feasible assignment exists that satisfies all such constraints, these become _soft_ and their violations are penalised by a weighted cost.

The objective is to **minimise the total weighted cost** of violated soft inequality constraints. Hard equality constraints must always be satisfied.

This problem was introduced by the French military electronics agency **CELAR** (Centre d'Electronique de l'ARmement) and is a widely studied benchmark in constraint programming and optimisation. It was used in the **MiniZinc Challenge 2013 and 2016**.

> Cabon, B., de Givry, S., Lobjois, L., Schiex, T., & Warners, J. P. (1999).
> **Radio Link Frequency Assignment.**
> _Constraints_, 4(1), 79–89.
> https://doi.org/10.1023/A:1026488913529

---

## Inputs

| Parameter              | Description                                                             |
| ---------------------- | ----------------------------------------------------------------------- |
| `costs`                | Array of 4 penalty weights, one per soft-constraint weight category     |
| `num_categories`       | Number of distinct frequency domain categories                          |
| `categories`           | For each category, the set of permitted integer frequencies             |
| `min_freq`, `max_freq` | Global lower and upper bounds on all frequencies                        |
| `num_variables`        | Number of communication links (frequency variables)                     |
| `domains`              | For each link, the index of its permitted frequency category            |
| `num_hardconstraints`  | Number of hard equality constraints                                     |
| `hardctrx`, `hardctry` | Indices of the two links involved in each hard constraint               |
| `hardctrk`             | Required absolute frequency difference for each hard constraint         |
| `num_softconstraints`  | Number of soft inequality constraints                                   |
| `softctrx`, `softctry` | Indices of the two links involved in each soft constraint               |
| `softctrk`             | Minimum required absolute frequency difference for each soft constraint |
| `softctrw`             | Weight category index for each soft constraint (indexes into `costs`)   |

---

## Decision Variables

| Variable    | Meaning                                                      |
| ----------- | ------------------------------------------------------------ |
| `f[i]`      | The integer frequency assigned to communication link `i`     |
| `objective` | The total weighted penalty for all violated soft constraints |

---

## Objective

Minimise `objective`, which accumulates the penalty weight `costs[softctrw[j]]` for every soft constraint `j` whose frequency separation condition is _not_ met (i.e. where $|f_x - f_y| \leq k$). Hard equality constraints are never penalised — they must be satisfied exactly.

---

## Instances

The benchmark includes instances from the original CELAR dataset (`CELAR6` and `CELAR7` sub-instances) as well as additional graph-based and scenario instances (`graph05`, `graph11`, `scen06`, `scen07`). These range from small sub-problems to larger, harder scenarios used to stress-test solvers.
