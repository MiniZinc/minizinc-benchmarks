# Elementary Flux Mode Enumeration in Metabolic Networks (`network_50_cstr`)

## Problem Description

This model finds **Elementary Flux Modes (EFMs)** in a biochemical reaction network. An EFM is one of the simplest possible ways a set of reactions in a metabolic network can operate together while keeping all internal chemical compounds in balance (a condition known as _steady state_). Finding EFMs is important in systems biology and metabolic engineering because they represent the fundamental building blocks of all feasible metabolic behaviours.

Intuitively, imagine a factory (the cell) with many possible production lines (reactions). An EFM is the smallest possible subset of production lines that can run simultaneously such that nothing accumulates and nothing runs out inside the factory.

The model finds the **minimum-size** EFM — the one that involves the fewest active reactions.

## Parameters (Input Data)

| Parameter | Description                                                                                                                                             |
| --------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `n`       | Number of reactions in the network                                                                                                                      |
| `m`       | Number of metabolites (chemical compounds)                                                                                                              |
| `k`       | Number of reversible reactions (reactions that can run in both directions)                                                                              |
| `Rs`      | Names/labels of reactions                                                                                                                               |
| `Ms`      | Names/labels of metabolites                                                                                                                             |
| `S`       | Stoichiometry matrix (`m × n`): encodes how much of each metabolite is consumed or produced by each reaction (negative = consumed, positive = produced) |
| `Revs`    | Reversibility indicator matrix (`k × n`): describes which reactions are grouped as reversible pairs                                                     |

## Decision Variables

| Variable | Type                                           | Description                                                                                                                                   |
| -------- | ---------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- |
| `Vs`     | Integer array, range `0..50`, one per reaction | The **flux** (rate) of each reaction. A value of zero means the reaction is inactive; a positive value means it is active at that rate.       |
| `Zs`     | Boolean array, one per reaction                | The **support** of the flux vector: `true` if the corresponding reaction is active (`Vs > 0`), `false` otherwise. This is the primary output. |

## Constraints

1. **Non-trivial solution**: At least one reaction must be active (the all-zeros solution is excluded).
2. **Non-negativity**: All flux values are non-negative (fluxes are represented in a forwards direction only).
3. **Support linkage**: A reaction is active (`Zs[j] = true`) if and only if its flux is strictly positive (`Vs[j] > 0`).
4. **Steady-state condition** (`Sv = 0`): For every metabolite, the total amount produced equals the total amount consumed across all active reactions. This ensures the network is in chemical balance.
5. **Reversibility constraints**: For each reversible reaction, at most one of its two possible directions can be active simultaneously. This encodes thermodynamic feasibility.

## Objective

**Minimise** the number of active reactions — i.e., minimise `sum(Zs)`. This finds the smallest possible EFM (the one with the fewest reactions), which corresponds to the most elementary or primitive metabolic pathway.

## Instances

The benchmark instances use real metabolic network data. Instance names such as `MODEL1507180015` correspond to models from the [BioModels Database](https://www.ebi.ac.uk/biomodels/), a public repository of mathematical models of biological systems.

## References

This model was authored by **Maxime Mahout** and **François Fages** (© 2024, MIT License), researchers at Inria, France. Their work applies constraint programming to enumerate EFMs efficiently, particularly for genome-scale metabolic networks.

Relevant background literature:

- Mahout, M., & Fages, F. (2024). _Constraint Programming for Elementary Flux Mode Enumeration_. Proceedings of the 30th International Conference on Principles and Practice of Constraint Programming (CP 2024). _(Reference inferred from authorship and context — please verify.)_
- Klamt, S., Saez-Rodriguez, J., & Gilles, E. D. (2007). Structural and functional analysis of cellular networks with CellNetAnalyzer. _BMC Systems Biology_, 1, 2.
- Schuster, S., Dandekar, T., & Fell, D. A. (1999). Detection of elementary flux modes in biochemical networks: a promising tool for pathway analysis and metabolic engineering. _Trends in Biotechnology_, 17(2), 53–60.

> **Note**: The exact publication associated with this specific model file has been inferred from the copyright notice. If you have access to the original paper, please update this reference.

## Model update summary

Added concise inline comments in efm_cstr.mzn to clarify:

- flux/support decision variable semantics,
- objective interpretation as minimal support size,
- minimization intent for compact feasible flux modes.
