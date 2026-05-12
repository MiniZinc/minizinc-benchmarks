# De Bruijn Sequences

## Problem Description

A **de Bruijn sequence** for an alphabet of size `base` and word length `n` is a cyclic sequence of symbols such that every possible word of length `n` over that alphabet appears **exactly once** as a contiguous substring. For example, with a binary alphabet (`base = 2`) and word length `n = 3`, the sequence `00010111` is a de Bruijn sequence: reading it cyclically, the eight 3-bit windows `000`, `001`, `010`, `101`, `011`, `111`, `110`, `100` are all distinct and cover every possible 3-bit string.

The total length of the sequence is `m = base^n`, which is also the number of distinct n-length words over the alphabet.

This model finds a valid de Bruijn sequence (or verifies that one exists) for given values of `base` and `n`. It also supports generalised (non-classical) variants where `m` is not necessarily equal to `base^n`, though the data files provided use the classical case.

## Parameters

| Parameter | Description                                                                                             |
| --------- | ------------------------------------------------------------------------------------------------------- |
| `base`    | The size of the alphabet; symbols are drawn from `0, 1, ..., base-1`. For binary sequences, `base = 2`. |
| `n`       | The word length; every contiguous window of `n` symbols in the cyclic sequence must be unique.          |
| `m`       | Derived as `ceil(base^n)` — the length of the sequence.                                                 |

## Decision Variables

| Variable             | Description                                                                                                                                                                                                 |
| -------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `x[1..m]`            | The sequence of integer values `0` to `base^n - 1`, each appearing exactly once. Each element represents one n-digit word encoded as a single integer.                                                      |
| `binary[1..m, 1..n]` | A 2D array holding the base-`base` digit representation of each element in `x`. Row `i` gives the `n` digits of `x[i]`.                                                                                     |
| `bin_code[1..m]`     | The actual output sequence of symbols. Each entry is the leading digit of the corresponding row of `binary`, i.e. `bin_code[i] = binary[i, 1]`. Reading `bin_code` cyclically gives the de Bruijn sequence. |
| `gcc[0..base-1]`     | The count of how many times each symbol `0, 1, ..., base-1` occurs in `bin_code`. When `m` is divisible by `base`, all counts are constrained to be equal.                                                  |

## Constraints

1. **All words are distinct** — the values in `x` are all different, ensuring every possible n-digit word appears exactly once.
2. **Overlap condition (de Bruijn property)** — the digit representation of each consecutive pair `binary[i]` and `binary[i+1]` must overlap by `n-1` digits: the last `n-1` digits of `binary[i]` equal the first `n-1` digits of `binary[i+1]`. This wraps around cyclically so the sequence forms a closed loop.
3. **Symbol balance** — when `m mod base = 0`, every symbol must appear the same number of times in `bin_code`.
4. **Symmetry breaking** — the first element `x[1]` is constrained to be the minimum value, eliminating rotationally equivalent solutions.

## Objective

This is a **satisfaction** problem — there is no objective function to optimise. The goal is to find any valid de Bruijn sequence satisfying all constraints.

## Example Instances

The data files are named `{base}_{n}.json`. For instance, `02_03.json` sets `base = 2` and `n = 3`, producing a classic binary de Bruijn sequence of length 8. Larger instances such as `04_08.json` (`base = 4`, `n = 8`) yield sequences of length `4^8 = 65536`.

## References

- N. G. de Bruijn, "A combinatorial problem," _Koninklijke Nederlandse Akademie van Wetenschappen, Proceedings_, vol. 49, pp. 758–764, 1946. The original paper introducing these sequences.
- Hakan Kjellerstrand, MiniZinc model and Swedish blog post: <http://www.hakank.org/webblogg/archives/001209.html>
- Interactive de Bruijn sequence generators by the same author: <http://www.hakank.org/comb/debruijn.cgi>

## Model update summary

Added concise inline comments in debruijn_binary.mzn to clarify:

- the core sequence variables (x, binary, bin_code, gcc),
- the cyclic n-1 overlap condition defining de Bruijn adjacency,
- the wrap-around overlap from the last word back to the first.
