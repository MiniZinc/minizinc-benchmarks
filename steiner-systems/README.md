# Steiner Systems Model

## **Overview**

This MiniZinc model constructs a **Steiner system** \(denoted as \( S(t, k, N) \)\). A Steiner system is a combinatorial design consisting of:

- A set \( X \) of size \( N \).
- A collection \( C \) of subsets of \( X \) called **blocks**, each of size \( k \).
- The property that **every subset of \( t \) elements from \( X \) appears in exactly one block**.

Steiner systems are widely used in combinatorial design theory, coding theory, and experimental design.

---

## **Problem Description**

Given integers:

- \( t \): Size of subsets that must appear exactly once in the blocks.
- \( k \): Size of each block.
- \( N \): Size of the universal set \( X \).

The model ensures:

- Each block has exactly \( k \) elements.
- Any two blocks intersect in at most \( t - 1 \) elements.
- The total number of blocks \( m \) is:
  \[
  m = \frac{\binom{N}{t}}{\binom{k}{t}}
  \]

---

## **Parameters**

- `int: t` — Subset size for uniqueness.
- `int: k` — Block size.
- `int: N` — Size of the universal set.

Derived:

- `set of int: X = 1..N` — The universal set.
- `int: m` — Number of blocks, computed as:
  ```minizinc
  m = nCr(N, t) div nCr(k, t);
  ```

---

## **Decision Variables**

- `array[1..m] of var set of X: C`  
  Represents the collection of blocks. Each block is a set of elements from ( X ).

---

## **Constraints**

1.  **Block Size:**  
    Each block contains exactly ( k ) elements:

    ```minizinc
    card(C[i]) = k;
    ```

2.  **Intersection Limit:**  
    Any two blocks share at most ( t - 1 ) elements:

    ```minizinc
    card(C[i] intersect C[j]) <= t - 1;
    ```

3.  **Symmetry Breaking:**  
    Blocks are ordered to reduce equivalent solutions:
    ```minizinc
    C[i] < C[i+1];
    ```

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

The goal is to **find any valid Steiner system** satisfying the constraints.

---

## **Applications**

- Error-correcting codes.
- Network design.
- Experimental design in statistics.
- Cryptography.

---

## **References**

- Steiner Systems: <https://en.wikipedia.org/wiki/Steiner_system>
- Design Theory: _Combinatorial Designs: Principles and Applications_ by C.J. Colbourn and J.H. Dinitz.

---
