# MiniZinc Model: Mono-Matching Game (Dobble/Spot-It)

## **Overview**

This MiniZinc model represents a **mono-matching game**, commonly known as **Dobble** or **Spot-It**. The game consists of a set of cards, each containing a fixed number of symbols, with the property that **every pair of cards shares exactly one symbol**. This model demonstrates how to construct such a set of cards using basic set constraints, serving primarily as a **stress test for set variables** rather than an efficient construction method.

### **Background**

Mono-matching games are mathematically related to **finite projective planes** and **cyclic difference sets**, which provide systematic ways to generate these card sets. However, this model uses a direct approach without leveraging those advanced constructions.

---

## **Problem Description**

- **Goal:** Generate a collection of cards such that:

  - Each card contains exactly `n` symbols.
  - Every pair of distinct cards shares **exactly one symbol**.
  - All cards are unique.

- **Inputs:**

  - `int: n`  
    The order of the set, which determines the number of symbols per card.
  - `float: card_percentage`  
    The fraction of possible cards to include in the game.

- **Derived Values:**
  - `int: items = n * n + n + 1`  
    Total number of symbols available (based on projective plane properties).
  - `set of int: Cards = 1..floor(items * card_percentage)`  
    The set of card indices.
  - `set of int: Symbols = 1..items`  
    The set of symbol indices.

---

## **Decision Variables**

- `array[Cards] of var set of Symbols: cards`  
  Each element represents the set of symbols on a card.

---

## **Constraints**

1. **Card Size Constraint:**  
   Each card must contain exactly `n` symbols:

   ```minizinc
   constraint forall(c in cards) ( card(c) == n );

   ```

2. **Pairwise Intersection Constraint:**  
   Every pair of distinct cards shares exactly one symbol:

   ```minizinc
   constraint forall(i, j in Cards where i < j) (
       card(cards[i] intersect cards[j]) == 1
   );
   ```

3. **Uniqueness Constraint:**  
   All cards must be different:
   ```minizinc
   constraint all_different(cards);
   ```

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

This means the goal is **feasibility**—finding any set of cards that satisfies the constraints.

---

## **Notes**

- This model is **not optimised** for large instances; it is intended as a **stress test for set variables**.
- Efficient generation of such games typically uses **finite projective planes** or **difference sets**.
- Licensed under the [MIT License](https://opensource.org/licenses/MIT).

---

## **References**

- [Dobble (Spot-It) on Wikipedia](https://en.wikipedia.org/wiki/Dobble)
- Related mathematical concepts: _Finite Projective Planes_, _Cyclic Difference Sets_.

---
