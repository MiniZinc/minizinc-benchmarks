# MiniZinc Model: SPECK Cipher Differential Optimisation

## **Overview**

This MiniZinc model focuses on analysing and optimising **differential characteristics** of the SPECK block cipher, a lightweight cryptographic algorithm designed for efficiency in constrained environments. The goal is to find characteristics that minimise the cumulative probability of differences across multiple rounds of the cipher.

---

## **Problem Description**

- **Cipher:** SPECK is a family of lightweight block ciphers using simple operations such as modular addition, bitwise XOR, and rotations.
- **Objective:** Identify a sequence of differences through `nr` rounds that minimises the sum of probabilities associated with modular additions. This helps in evaluating the cipher's resistance to differential cryptanalysis.

---

## **Parameters**

- `int: n`  
  Word size (e.g., 16 or 32 bits).
- `int: nr`  
  Number of rounds in the cipher.
- `int: lr`  
  Left rotation constant (depends on `n`).
- `int: rr`  
  Right rotation constant (depends on `n`).

---

## **Decision Variables**

- `array[0..nr, 0..n-1] of var bool: L`  
  Left word differences for each round.
- `array[0..nr, 0..n-1] of var bool: R`  
  Right word differences for each round.
- `array[0..nr-1] of var 0..n: p`  
  Probability cost for each round based on modular addition differences.
- `var 0..n*4: objective`  
  Sum of all probability costs across rounds (to be minimised).

---

## **Constraints**

1. **Non-zero Difference:**  
   The initial state must have at least one bit difference:

   ```minizinc
   sum(row(L, 0) ++ row(R, 0)) > 0;
   ```

2. **Round Function:**  
   For each round:

   - Compute new left word using modular addition and rotations.
   - Compute new right word using XOR and rotations:

   ```minizinc
   modular_addition_word(RRot(L[i], rr), R[i], L[i+1], p[i]) /\
   R[i+1] = XOR(L[i+1], LRot(R[i], lr));
   ```

3. **Probability Calculation:**  
   The `modular_addition_word` predicate calculates the number of uncertain carry positions, which influences the differential probability.

---

## **Objective**

Minimise:

```minizinc
objective = sum(p);
```

This corresponds to finding the most probable differential trail through the cipher.

---

## **Applications**

- Cryptanalysis of lightweight block ciphers.
- Security evaluation for IoT and embedded systems.
- Research in differential cryptanalysis techniques.

---

## **References**

- SPECK cipher specification by the NSA.
- Differential cryptanalysis principles in modern block ciphers.

---
