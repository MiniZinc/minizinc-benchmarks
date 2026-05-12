# Optimal Differential Cryptanalysis

## Problem Description

This model searches for the **optimal differential characteristic** of the [PRESENT](https://en.wikipedia.org/wiki/PRESENT) block cipher, a lightweight 64-bit block cipher designed for constrained environments such as RFID tags and embedded devices.

**Differential cryptanalysis** is a classical technique for attacking block ciphers. The idea is to trace how a chosen _difference_ between two plaintexts propagates through the rounds of a cipher. If a difference follows a specific path (called a _differential characteristic_) with high enough probability, it can be exploited to recover secret key information. Finding the most probable such path over a given number of rounds tells us how resistant the cipher is to this type of attack.

> **Note:** Despite the filename (`mznc2017_aes_opt.mzn`) suggesting a connection to AES, the cipher structure encoded in this model — a 64-bit block, 16 parallel 4-bit S-boxes, and a specific bit permutation — matches PRESENT exactly, not AES. The "aes" label in the filename may refer to the style of analysis or be a misnaming. An expert familiar with the MiniZinc Challenge 2017 submission history may be able to clarify this.

### Cipher Structure

PRESENT operates on a 64-bit state divided into 16 nibbles (4-bit groups). Each round applies two layers:

1. **Substitution layer (SBoxes):** Each of the 16 nibbles is passed through a 4-bit S-box (a small lookup table that introduces non-linearity).
2. **Permutation layer:** The 64 bits are rearranged according to a fixed bit permutation, spreading differences across the state.

This model analyses `R` rounds of this structure.

---

## Model Variables

| Variable    | Meaning                                                                                                                                                                                                                                                                                                                                                                                                           |
| ----------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `R`         | Number of rounds (given as input data).                                                                                                                                                                                                                                                                                                                                                                           |
| `x[r, b]`   | A binary variable (0 or 1) representing whether bit `b` is "active" (i.e., carries a non-zero difference) at the start of round `r`. There are `R+1` such states, from the input (`r=0`) to the output (`r=R`).                                                                                                                                                                                                   |
| `xp[r, b]`  | A binary variable representing the state of bit `b` after the permutation in round `r`, but before the S-boxes of the next round. This is the intermediate state between the permutation and the next substitution layer.                                                                                                                                                                                         |
| `prb[i]`    | The probability weight assigned to S-box `i` (across all rounds). Its value is drawn from the set `{0, 2, 3}`, representing: **0** = the S-box is inactive (difference passes through trivially, probability = 1); **2** = the S-box is active with probability $2^{-2}$; **3** = the S-box is active with probability $2^{-3}$. These are negative base-2 logarithms of the differential transition probability. |
| `objective` | The total probability weight: the sum of all `prb[i]` values. This equals the total $-\log_2$ of the probability of the differential characteristic.                                                                                                                                                                                                                                                              |

---

## Data: The Difference Distribution Table (DDT)

The constant array `DDT` encodes all valid differential transitions through the 4-bit S-box. Each row specifies a 4-bit input difference (in binary), a 4-bit output difference (in binary), and the corresponding probability weight (0, 2, or 3). Only transitions with non-zero probability appear. There are 97 such valid transitions.

The `table` global constraint is used to enforce that each S-box's input/output difference pair is consistent with one of these valid DDT entries.

The permutation array `P` encodes PRESENT's bit permutation: bit at position `j` moves to position `P[j]` after the permutation layer.

---

## Objective

The model **minimises** the `objective`, which is the sum of all S-box probability weights across all rounds. A smaller value means a more probable differential characteristic, which corresponds to a potentially stronger attack on the cipher. Conversely, if even the best characteristic has a very high total weight (very low probability), the cipher is considered more resistant to differential attacks.

The model also includes **Matsui-style boundary constraints**: S-boxes in the very first and last rounds are restricted to weights of 0 or 2 only (not 3). This is a pruning technique inspired by Matsui's algorithm for finding optimal linear/differential characteristics, which tightens the search by bounding partial characteristics.

---

## Instances

Instances are parameterised by the number of rounds `R`. The benchmark suite includes instances ranging from `R=1` to `R=15`, with larger values of `R` being significantly harder to solve.

---

## References

- A. Bogdanov, L. R. Knudsen, G. Leander, C. Paar, A. Poschmann, M. J. B. Robshaw, Y. Seurin, C. Vikkelsoe. **PRESENT: An Ultra-Lightweight Block Cipher.** _CHES 2007_, LNCS 4727, pp. 450–466. Springer, 2007.
- E. Biham, A. Shamir. **Differential Cryptanalysis of DES-like Cryptosystems.** _Journal of Cryptology_, 4(1):3–72, 1991.
- This problem appeared in the **MiniZinc Challenge 2017, 2018, and 2021**.

## Model update summary

Added concise inline comments in mznc2017_aes_opt.mzn to clarify:

- round-state decision variable roles,
- objective semantics as differential weight,
- minimization intent for best trail probability bound.
