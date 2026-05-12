# Free Pizza Voucher Optimisation

## Overview

This MiniZinc model chooses how to apply a set of pizza vouchers in order to **minimise the amount paid** for an order.

The input gives a list of pizza prices and a list of vouchers. Each voucher has the form **buy `x`, get `y` free**. When a voucher is used, the pizzas counted as _free_ must not be more expensive than the pizzas counted as _paid_ for that same voucher. In other words, the customer must pay for the more expensive pizzas and can only get cheaper pizzas for free.

At a high level, this is a **discount allocation** problem: given several pizzas and several vouchers, decide which pizzas should be paid for normally, which should be attached to vouchers as required purchases, and which can be taken for free.

## Problem being solved

The model answers the following question:

> Given an order of pizzas and a collection of available vouchers, what is the cheapest valid way to assign pizzas to those vouchers?

A pizza may either:

- be paid for without using any voucher,
- be counted as one of the pizzas that must be bought for a voucher,
- or be counted as one of the pizzas received for free from a voucher.

Each voucher in the input can be used **at most once**. If it is used, enough pizzas must be assigned to its “buy” side, and no more than the allowed number may be assigned to its “free” side.

## Main data and decision variables

### Input data

- `n`: number of pizzas.
- `price[p]`: price of pizza `p`.
- `m`: number of vouchers.
- `buy[v]`: how many pizzas must be paid for to activate voucher `v`.
- `free[v]`: how many pizzas may be free under voucher `v`.

### Decision variables

- `how[p]`: describes what happens to pizza `p`.
  - `0` means the pizza is not attached to any voucher and is paid for normally.
  - `-v` means the pizza is assigned to the **paid** part of voucher `v`.
  - `v` means the pizza is assigned to the **free** part of voucher `v`.
- `used[v]`: true when voucher `v` is actually used.

This signed encoding lets the model represent both sides of a voucher with a single variable for each pizza.

## Key rules enforced by the model

The model enforces these ideas:

1. **A used voucher must have enough paid pizzas.**  
   If voucher `v` is used, at least `buy[v]` pizzas must be assigned to its paid side.

2. **A voucher cannot claim too many pizzas.**  
   No voucher may have more paid pizzas than required, and no voucher may have more free pizzas than allowed.

3. **Free pizzas must not be more expensive than the paid pizzas for the same voucher.**  
   This captures the usual shop rule that the customer pays for the most expensive items.

These constraints together make sure every discount assignment is valid.

## Objective

The optimisation variable `objective` is the **total amount actually paid**.

It adds the prices of:

- pizzas not using any voucher, and
- pizzas assigned to the paid side of vouchers.

Pizzas assigned to the free side do not contribute to the objective. The solver therefore looks for the voucher assignment that gives the **lowest total bill**.

## Notes and uncertainty

From the model, the interpretation of the problem is clear: it is about optimally applying pizza vouchers under a “pay for the expensive pizzas, get cheaper ones free” rule.

However, the file does **not** state the original business source, competition statement, or paper from which the benchmark was derived. Also, the model treats each voucher entry as a separate voucher instance, so repeated voucher types would need to appear multiple times in the input if they are available multiple times.

## References

- Included in this repository as the MiniZinc benchmark **freepizza**.
- The local metadata indicates that it appeared in the **MiniZinc Challenge 2015** benchmark set.
- No explicit academic paper or original problem-source citation is included in the model or metadata, so the exact literature source could not be confirmed from the available files.

## Model update summary

Added concise inline comments in freepizza.mzn to clarify:

- voucher-assignment decision variable semantics,
- objective interpretation as total paid amount,
- that edits are readability-only and behavior-preserving.
