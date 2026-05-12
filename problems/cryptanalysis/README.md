# Chosen-Key Differential Cryptanalysis of AES

## Overview

This model encodes the first step of a **chosen-key differential cryptanalysis** attack on the AES (Advanced Encryption Standard) block cipher. The goal is to find a **differential characteristic** — a pattern describing how carefully chosen differences in plaintext and encryption key propagate through multiple rounds of AES — while minimising the number of "active" bytes (bytes that carry a non-zero difference).

Finding such characteristics with few active bytes is the core challenge in differential cryptanalysis, since fewer active bytes generally correspond to a more powerful attack against the cipher.

This model was introduced in the paper:

> David Gerault, Marine Minier, Christine Solnon.  
> _Constraint Programming Models for Chosen Key Differential Cryptanalysis._  
> CP 2016 — 22nd International Conference on Principles and Practice of Constraint Programming.

---

## Background: AES and Differential Cryptanalysis

AES operates on a 128-bit block of data, organised as a 4×4 matrix of bytes. Each round of AES applies four operations in sequence:

1. **AddRoundKey (ARK)** — XOR the data with a round-specific key.
2. **SubBytes (SB)** — Apply a non-linear substitution to each byte.
3. **ShiftRows (SR)** — Cyclically shift each row of the matrix.
4. **MixColumns (MC)** — Multiply each column by a fixed matrix (providing diffusion).

In **differential cryptanalysis**, instead of tracking the actual byte values, we track binary _difference indicators_: for each byte position, does a difference exist (1) or not (0)? The attacker also controls differences in the key (chosen-key setting).

The **key schedule** is the procedure AES uses to derive a series of round keys from the original key. This model explicitly tracks how key differences propagate through the key schedule.

---

## Parameters

| Parameter   | Description                                                                             |
| ----------- | --------------------------------------------------------------------------------------- |
| `n`         | Number of rounds of AES to analyse                                                      |
| `KEY_BITS`  | Number of bits in the key (128 for AES-128, 192 for AES-192, 256 for AES-256)           |
| `objective` | The target total number of active bytes (used to check satisfiability at a given bound) |

Derived constants `KC` (key columns per round), `BC` (block columns per round), and `NBK` (total key component variables) are computed from these parameters.

---

## Decision Variables

All variables are binary (0 = no difference, 1 = difference present), operating at the level of individual bytes within the AES state or key matrix.

| Variable                 | Dimensions                       | Meaning                                                                                                         |
| ------------------------ | -------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| `deltaX[r][j][i]`        | round × column × row             | Difference in state byte `(i,j)` **after AddRoundKey** in round `r`                                             |
| `deltaY[r][j][i]`        | round × column × row             | Difference in state byte `(i,j)` **before AddRoundKey** (i.e., after MixColumns) in round `r`                   |
| `deltaSR[r][j][i]`       | round × column × row             | Difference in state byte `(i,j)` **after ShiftRows** in round `r`                                               |
| `deltaK[r][j][i]`        | round × column × row             | Difference in round key byte `(i,j)` in round `r`                                                               |
| `Kcomp[r][j][i][k]`      | round × column × row × component | Binary component decomposition of `deltaK`, tracking which original key bytes contribute to each round key byte |
| `eqK[i][r1][j1][r2][j2]` | row × two (round,column) pairs   | Whether key bytes at positions `(r1,j1)` and `(r2,j2)` in row `i` carry **equal** differences                   |
| `colX[r][j]`             | round × column                   | Number of active bytes (0–4) in column `j` of the state after ARK in round `r`                                  |
| `colSRX[r][j]`           | round × column                   | Number of active bytes (0–4) in column `j` after ShiftRows in round `r`                                         |
| `colK[r][j]`             | round × column                   | Number of active bytes (0–4) in column `j` of the round key in round `r`                                        |

---

## Constraints

### AddRoundKey (ARK)

XOR of the state difference before ARK with the round key difference gives the state difference after ARK. Because XOR in the difference domain allows 1⊕1 = 0 or 1, the constraint simply excludes the (1,0,0) / (0,1,0) / (0,0,1) patterns.

### ShiftRows (SR)

A permutation of bytes: byte `(i,j)` after ShiftRows corresponds to byte `(i, (j+i) mod BC)` before it. Differences are simply permuted accordingly.

### MixColumns (MC)

MixColumns is an **MDS (Maximum Distance Separable)** transformation. This means: if a column entering MixColumns has between 1 and 3 active bytes, then together the column before and after MixColumns must have at least 5 active bytes in total. This MDS property is enforced as a linear constraint on the column byte counts.

### Key Schedule (KS)

Key differences propagate through the AES key schedule. Every new round key byte is derived via XOR of previous key bytes (and SubBytes at certain positions). The `Kcomp` variables decompose each round key difference into its originating key byte components, enabling equality detection between key bytes.

### Equality Relations (EQrelations)

Tracks when two round key bytes are guaranteed to carry the same difference. Enforces symmetry and transitivity of equality, and links the `eqK` indicators back to the `deltaK` and `Kcomp` variables.

### Linear MixColumns (linearMC)

An additional propagation rule: if two distinct column positions produce different outputs from SubBytes (in terms of byte differences), the MDS property must hold for those positions jointly. This strengthens the model by exploiting pairwise relationships between columns.

---

## Objective / Solve Goal

The model is a **satisfaction** problem: it checks whether a valid differential characteristic exists for **exactly** the given `objective` value, where `objective` is the sum of:

- All active bytes in the ShiftRows output across all rounds and columns, plus
- Active bytes in selected key schedule columns.

To find the _minimum_ possible `objective` value (the hardest-to-achieve characteristic), this model would typically be called repeatedly with decreasing values of `objective` until no solution exists — or used together with a second step (this file is named `step1_aes.mzn`, implying a multi-step pipeline).

---

## Notes and Uncertainties

- The naming convention `step1_aes.mzn` suggests this is the first phase of a two-step process. The second step likely uses the output differential pattern found here to verify or extend the attack. The exact pipeline is not documented within this file.
- The `objective` parameter is provided externally (via a data file), meaning the model does not minimise directly — it tests feasibility at a given bound.
- The `Kcomp` representation (decomposing key differences into their originating key material components) is a novel encoding introduced in the referenced CP 2016 paper to track key equality relationships that would otherwise be lost.
- An expert familiar with the full benchmark suite may wish to confirm which data files (`.dzn`) correspond to which AES variant (AES-128, AES-192, AES-256) and number of rounds.

---

## Reference

Gerault, D., Minier, M., & Solnon, C. (2016).  
_Constraint Programming Models for Chosen Key Differential Cryptanalysis._  
In _Proceedings of the 22nd International Conference on Principles and Practice of Constraint Programming (CP 2016)_, Lecture Notes in Computer Science, vol. 9892. Springer, Cham.  
https://doi.org/10.1007/978-3-319-44953-1_24

## Model update summary

Added concise inline comments in step1_aes.mzn to clarify:

- AES difference-state variable roles (`deltaX`, `deltaY`, `deltaSR`, `deltaK`),
- feasibility-style objective-bound equation used in step 1,
- search-phase intent for objective-driving and bit-level variables.
