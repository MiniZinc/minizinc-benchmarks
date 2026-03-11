# Monomatch (Dobble / Spot-It Construction)

## Problem Description

This model constructs a **mono-matching game** — a card game where every pair of cards shares
exactly one symbol in common. The most commercially well-known version of this type of game is
[Dobble](https://en.wikipedia.org/wiki/Dobble) (sold as _Spot It!_ in North America).

In a mono-matching game you have a deck of cards and a collection of symbols. The defining
property is:

> **Any two cards in the deck have exactly one symbol in common.**

Mathematically, complete sets of such cards can be constructed from **finite projective planes** or
**cyclic difference sets**. For a plane of order _n_, there are exactly _n² + n + 1_ possible cards
and the same number of possible symbols, with each card carrying exactly _n + 1_ symbols.

**Note:** This model intentionally does _not_ use those algebraic constructions. Instead, it
expresses the problem directly using set-variable constraints, making it a stress test for solvers
that support set variables.

_Created by Mikael Zayenz Lagerkvist, 2021._

---

## Parameters

| Parameter         | Description                                                                   |
| ----------------- | ----------------------------------------------------------------------------- |
| `n`               | The **order** of the construction. Controls the size of the projective plane. |
| `card_percentage` | The **fraction** (0–1) of all possible cards to include in the deck.          |

From these two parameters the model derives:

- `items = n² + n + 1` — the total number of distinct symbols (and the maximum number of cards in
  a complete deck).
- `Cards = 1..floor(items × card_percentage)` — the indices of the cards actually created.
- `Symbols = 1..items` — the universe of available symbols.

---

## Decision Variables

| Variable   | Type                 | Meaning                                     |
| ---------- | -------------------- | ------------------------------------------- |
| `cards[c]` | `var set of Symbols` | The **set of symbols** printed on card _c_. |

Each element of `cards` is a set-valued decision variable — the solver must choose which symbols
appear on each card.

---

## Constraints

1. **Fixed card size:** Every card carries exactly _n_ symbols.
   $$|cards_c| = n \quad \forall c \in Cards$$

2. **Unique shared symbol:** Every pair of distinct cards shares exactly one symbol.
   $$|cards_i \cap cards_j| = 1 \quad \forall i, j \in Cards,\ i < j$$

3. **Distinct cards:** No two cards are identical (`all_different`).

---

## Objective

This is a **satisfaction** problem — there is no objective to optimise. The goal is simply to find
an assignment of symbols to cards that satisfies all three constraints above.

---

## Notes

- The full deck (with `card_percentage = 1.0`) corresponds to all _n² + n + 1_ cards of a
  projective plane of order _n_. Partial decks with `card_percentage < 1.0` reduce the number of
  cards, making the problem easier.
- The model is explicitly described by its author as a **stress test for set-variable reasoning**,
  rather than as an efficient construction algorithm.
- The model requires each card to have exactly _n_ symbols rather than _n + 1_ as in the classical
  projective-plane construction. This is a slight deviation from the standard definition; the
  classical Dobble deck for order _n_ has _n + 1_ symbols per card. The precise intended
  interpretation may warrant verification with the original author.

---

## References

- Wikipedia — [Dobble](https://en.wikipedia.org/wiki/Dobble)
- Wikipedia — [Projective plane](https://en.wikipedia.org/wiki/Projective_plane)
- Zayenz Lagerkvist, M. (2021). _Monomatch MiniZinc model._ MIT License.
