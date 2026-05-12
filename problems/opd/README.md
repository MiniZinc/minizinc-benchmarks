# Optimal Pairwise Design (OPD)

## Problem Description

An **Optimal Pairwise Design (OPD)** problem asks for the construction of a binary matrix (a grid of 0s and 1s) with `v` rows and `b` columns such that:

1. Every row contains exactly `r` ones (i.e., each row sums to `r`).
2. The **overlap** between any two distinct rows — measured as the number of columns where both rows have a 1 (the dot product) — is as small as possible.

The goal is to **minimise** the largest such overlap, referred to as **lambda** (λ). When every pair of distinct rows has _exactly_ the same overlap, the structure becomes a **Balanced Incomplete Block Design (BIBD)**, a well-known combinatorial design.

This problem arises naturally in the design of **Collateralised Debt Obligations Squared (CDO²)** financial transactions. In that context, a CDO² is a financial product built from a portfolio of other CDOs. Each CDO (a row) selects `r` assets (columns) from a pool of `b` assets. Minimising the pairwise overlap between CDOs reduces the correlation between them, which is desirable for risk diversification. An OPD instance is therefore denoted **OPD(v, b, r)**.

## Parameters

| Name | Description                                               |
| ---- | --------------------------------------------------------- |
| `v`  | Number of rows (e.g., number of inner CDOs)               |
| `b`  | Number of columns (e.g., number of assets in the pool)    |
| `r`  | Number of 1s in each row (e.g., number of assets per CDO) |

## Variables

| Name        | Type                  | Description                                                                                                          |
| ----------- | --------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `m[i, j]`   | Binary (0 or 1)       | The incidence matrix. `m[i,j] = 1` means row `i` includes column `j`.                                                |
| `objective` | Integer ≥ `lb_lambda` | The value of λ — the maximum dot product (overlap) between any two distinct rows. This is the value being minimised. |

A computed **lower bound** (`lb_lambda`) for λ is derived analytically from the parameters `v`, `b`, and `r`, and is used to tighten the search.

## Objective

**Minimise** `objective` (λ), the maximum pairwise overlap between any two rows of the matrix.

## Constraints

- **Row sum constraint:** Every row must contain exactly `r` ones.
- **Overlap constraint:** For every pair of distinct rows, their dot product (number of shared 1-columns) must be at most λ.
- **Symmetry breaking:** Rows are ordered lexicographically (largest first), and columns are ordered lexicographically (largest first), to eliminate equivalent solutions that are mere permutations of rows or columns.

## Related Problems

- **BIBD (Balanced Incomplete Block Design):** A special case where every pair of rows has _exactly_ the same overlap (λ), not just at most λ. The data files labelled `small_bibd_*` correspond to known BIBD instances.
- **OPD vs PD:** An OPD minimises the _maximum_ pairwise overlap; a **Pairwise Design (PD)** is one where this minimum has been achieved.

## References

- Pierre Flener, Justin Pearson, Luis G. Reyna, Olof Sivertsson:
  _Design of Financial CDO Squared Transactions Using Constraint Programming._
  Constraints **12**(2):179–205, 2007.
  [https://doi.org/10.1007/s10601-006-9014-4](https://doi.org/10.1007/s10601-006-9014-4)

- Additional solution approaches referenced in the model:
  - Local Search with Variable Neighbourhood Search (VNS):
    [https://doi.org/10.1016/j.endm.2014.11.017](https://doi.org/10.1016/j.endm.2014.11.017)
  - Constraint-Based Local Search (CBLS) with set variables:
    [https://doi.org/10.1007/11564751_7](https://doi.org/10.1007/11564751_7)

## Model Authors

Pierre Flener and Jean-Noël Monette (model loosely based on Ralph Becket's BIBD model).

## Model update summary

Added concise inline comments in opd.mzn to clarify:

- incidence-matrix decision variable semantics,
- objective meaning as minimized lambda overlap,
- optimization intent for low-correlation pairwise designs.
