# MiniZinc Model: Perfect Square (Squared Square) Problem

## **Overview**

This MiniZinc model solves the **Perfect Square Problem**, also known as the **Squared Square Problem**. The challenge is to pack a given set of smaller squares into a larger square without overlaps, ensuring that all squares fit perfectly within the boundaries of the larger square.

The problem is described in _"A Note on Perfect Square Placement"_ by N. Beldiceanu, E. Bourreau, and H. Simonis. It is a classic example of a **constraint satisfaction problem** involving geometric packing.

---

## **Problem Description**

- **Goal:** Arrange `n` smaller squares inside a larger square of size `size × size` such that:
  - All smaller squares are placed without overlapping.
  - Each square lies entirely within the boundaries of the larger square.

## **Parameters**

- `int: n`  
  Number of smaller squares to place.
- `int: size`  
  Dimension of the larger square.
- `array[1..n] of int: squars`  
  Sizes of the smaller squares (each entry represents the side length of a square).

---

## **Decision Variables**

- `array[1..n] of var 0..size: x`  
  X-coordinate of the top-left corner of each square.
- `array[1..n] of var 0..size: y`  
  Y-coordinate of the top-left corner of each square.

---

## **Constraints**

1. **Boundary Constraints:**  
   Each square must fit within the larger square:

   ```minizinc
   x[i] <= size - squars[i] /\ y[i] <= size - squars[i];
   ```

2. **Non-overlapping Constraint:**
   Squares must not overlap:
   ```minizinc
   diffn(x, y, squars, squars);
   ```
   The `diffn` global constraint ensures that all rectangles (in this case, squares) are placed without intersection.

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

This means the goal is to find **any feasible arrangement** of squares that satisfies all constraints.

---

## **Output**

The solution prints:

- X-coordinates of all squares.
- Y-coordinates of all squares.

---

## **References**

- N. Beldiceanu, E. Bourreau, H. Simonis: _A Note on Perfect Square Placement_.
- Related concept: _Geometric Packing Problems_ in combinatorial optimisation.

---
