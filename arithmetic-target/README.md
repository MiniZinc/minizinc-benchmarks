# Arithmetic Target Problem in MiniZinc

## Overview

This MiniZinc model solves the **Arithmetic Target Problem**, which is similar to the popular "Countdown" numbers game. The goal is to combine a given set of numbers using arithmetic operations (addition, subtraction, multiplication, and division) to reach a specified target value or get as close as possible.

The model constructs a binary expression tree representing the arithmetic operations applied to the numbers. It then evaluates the tree to compute the resulting value and minimises the difference between this value and the target.

---

## Problem Description

Given:

- A list of integers (`numbers`).
- A target integer (`target`).

We aim to:

- Use each number at most once.
- Combine numbers using the operations: **Add (+)**, **Sub (-)**, **Mul (\*)**, and **Div (/)**.
- Ensure division is exact (no remainder).
- Minimise the difference between the computed result and the target.

---

## Key Sets and Parameters

- `numbers`: Array of input integers.
- `target`: The desired result.
- `n`: Number of input integers.
- `N`: Index set for numbers (1..n).
- `M`: Index set for tree nodes (1..(2\*n - 1)).

### Tokens

The tree nodes can take values from:

- `Val`: A leaf node representing a number.
- `Add`, `Sub`, `Mul`, `Div`: Arithmetic operations.
- `Null`: Unused node.

---

## Decision Variables

- `tree[i]`: Type of node (operation or value).
- `left[i]`, `right[i]`: Indices of left and right child nodes.
- `indexes[i]`: Index of the number assigned to a leaf node.
- `tree_vals[i]`: Computed value of the subtree rooted at node `i`.
- `tree_depth`: Depth of the constructed tree.
- `used`: Number of numbers used in the expression.

---

## Constraints

1. **Tree Structure**:

   - Exactly `n` leaves with `Val` tokens.
   - Internal nodes represent valid operations.
   - Children of nodes follow binary tree rules.

2. **Value Assignment**:

   - Leaves correspond to input numbers.
   - Internal nodes compute values based on their operation and children.

3. **Division Constraint**:

   - Division is only allowed when the result is an integer (no remainder).

4. **Symmetry Breaking**:
   - Avoid equivalent expressions by enforcing ordering and associativity rules.
   - Examples:
     - No redundant identities (e.g., `a + 0`, `a * 1`).
     - Enforce sorted order for commutative operations (`a + b` vs `b + a`).

---

## Objective

Minimise:

$$
\text{Objective} = 10 \times | \text{tree\_vals}[1] - \text{target} | + \text{used}
$$

This prioritises closeness to the target while also considering the number of numbers used.

---

## Notes

- The model uses a binary tree representation to explore all possible arithmetic combinations.
- Symmetry-breaking constraints significantly reduce redundant solutions.
- If the target cannot be reached exactly, the model finds the closest possible value.

---

### References

- Inspired by arithmetic puzzle-solving and expression tree optimisation techniques.
