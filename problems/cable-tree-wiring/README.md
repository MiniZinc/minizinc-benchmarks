# Cable Tree Wiring

## Problem Description

This problem comes from the automotive manufacturing industry. A **cable harness** (or cable tree) is the bundle of wires that connects the many electrical components in a car. It is assembled by routing individual cables through a series of connectors, each of which has a set of numbered holes called **cavities**.

During harness assembly, a machine processes the cavities one at a time in a fixed linear sequence. The goal is to find the best ordering of all cavities so that the resulting wiring process is as efficient as possible.

This is a real-world industrial optimisation problem that has appeared in the MiniZinc Challenge (2020 and 2024).

## Parameters

| Parameter                | Meaning                                                                                                                                                                 |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `k`                      | Total number of cavities (across all connectors)                                                                                                                        |
| `b`                      | Number of cables; each cable connects exactly two cavities: cavity `i` and cavity `i+b` (for `i` in `1..b`)                                                             |
| `AtomicConstraints`      | Hard ordering rules: cavity A _must_ be processed before cavity B                                                                                                       |
| `DisjunctiveConstraints` | Flexible ordering rules: at least one of two ordering conditions must hold (with an additional consistency condition when the same cavity appears in both alternatives) |
| `DirectSuccessors`       | Adjacency rules: if the two ends of a specified cable happen to be ordered in a particular direction, they must be processed consecutively (no other cavity in between) |
| `SoftAtomicConstraints`  | Preferred ordering rules: cavity A _should_ be processed before cavity B, but violations are penalised rather than forbidden                                            |

## Decision Variable

`pfc[c]` — the **position** assigned to cavity `c` in the processing sequence. This is a permutation: every cavity gets a distinct position from `1` to `k`.

A redundant auxiliary array `cfp` (the inverse mapping from positions back to cavities) is also declared; it is kept consistent by an `inverse` constraint in spirit, though here it is marked as a `redundant_constraint` for solver performance.

## Objective

The objective is a **lexicographic minimisation** encoded as a single weighted integer:

$$\text{objective} = S \cdot k^3 + M \cdot k^2 + L \cdot k + N$$

Because `k^3 >> k^2 >> k >> 1` (for realistic values of `k`), minimising this scalar is equivalent to minimising the four components in strict priority order:

| Component | Priority      | Meaning                                                                                               |
| --------- | ------------- | ----------------------------------------------------------------------------------------------------- |
| `S`       | 1st (highest) | Number of cables whose two ends are **not** placed adjacently in the sequence                         |
| `M`       | 2nd           | Maximum number of open cables that **overlap** at any single position (i.e. the peak "crossing load") |
| `L`       | 3rd           | Maximum **span** of any single cable: the distance between its two ends minus one                     |
| `N`       | 4th (lowest)  | Number of violated **soft** ordering constraints                                                      |

Intuitively, the machine prefers cables whose two ends appear next to each other (minimising `S`), avoids having many cables "in flight" simultaneously (minimising `M`), keeps the longest cable short (minimising `L`), and respects preferred orderings where possible (minimising `N`).

## Constraints Summary

1. **All-different**: Every cavity is assigned a unique position in the sequence.
2. **Atomic (hard ordering)**: For each pair `(A, B)` in `AtomicConstraints`, cavity `A` must appear before cavity `B`.
3. **Disjunctive ordering**: For each row `(A, B, C, D)` in `DisjunctiveConstraints`, either `A` comes before `B` _or_ `C` comes before `D` (or both). An extra condition prevents a degenerate ordering when the first cavity in each alternative is the same.
4. **Direct successor**: If a cable's two ends end up ordered in the direction specified, they must be consecutive — no other cavity may be placed between them.
5. **Soft ordering (penalised)**: For each pair in `SoftAtomicConstraints`, a violation is counted in `N` if the preferred order is not respected.

## Notes

- The instances are named with a prefix of `A` (likely _automotive_) or `R` (possibly _random_ or a different category — the exact naming convention is uncertain and may benefit from clarification by the problem originator).
- This problem was submitted to the MiniZinc Challenge. For further background on the industrial context and constraint model, see:
  > Bart Bogaerts, Stephan Gocht, Ciaran McCreesh, Jakob Nordström. _Certified Symmetry and Dominance Breaking for Combinatorial Optimisation._ AAAI 2022. _(Note: this reference is tentative — the exact originating publication for this specific model is not confirmed and should be verified.)_

## Model update summary

Added concise inline comments in `ctw.mzn` to clarify:

- hard versus disjunctive precedence constraints,
- the direct-successor rule for paired chambers, and
- the interpretation and priority order of objective components `S`, `M`, `L`, and `N`.
