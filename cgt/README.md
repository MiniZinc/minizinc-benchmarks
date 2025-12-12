# Optimisation of Australian Capital Gains Tax

## Overview

This MiniZinc model optimises the calculation of **Australian Capital Gains Tax (CGT)** for a portfolio of stock trades. The goal is to minimise the taxable capital gains by determining the optimal matching of sold units to previously purchased units, considering the rules for CGT discounts and losses.

---

## Problem Description

In Australia, capital gains tax applies when you sell assets such as shares for more than their purchase price. Key rules include:

- **Discount rule**: If an asset is held for at least 12 months before selling, the gain is eligible for a 50% discount.
- **Loss offset**: Capital losses can offset capital gains.
- **FIFO or optimisation**: While many investors use FIFO (first-in-first-out), this model finds the optimal matching to minimise tax liability.

The model takes a list of trades (buys and sells) and determines which purchase each sold unit originated from, subject to legal constraints.

---

## Key Inputs

- `trades`: An array of records representing all trades, each with:
  - `date`: The time of the trade (in months).
  - `trade`: Type of trade (`Buy` or `Sell`).
  - `stock`: The stock identifier.
  - `units`: Number of units traded.
  - `price`: Price per unit.

From this, the model derives:

- `UNIT_BUY`: Individual purchased units.
- `UNIT_SELL`: Individual sold units.
- `unit_buys`: Details of each bought unit.
- `unit_sells`: Details of each sold unit.

---

## Decision Variable

- `origin[u]`: For each sold unit `u` (in `UNIT_SELL`), this variable indicates which bought unit (in `UNIT_BUY`) it came from.

---

## Constraints

1. **Unique Assignment**: Each bought unit can only be sold once (`all_different(origin)`).
2. **Temporal Validity**: A unit must be bought before it is sold.
3. **Symmetry Breaking**: Enforces a consistent ordering for units sold on the same date and stock to reduce redundant solutions.

---

## Calculations

- `discountable_gains`: Sum of gains from units held for **≥ 12 months**.
- `undiscountable_gains`: Sum of gains from units held for **< 12 months**.
- `losses`: Sum of losses where sale price < purchase price.
- `double_capital_gains`: A transformed value representing taxable gains × 2, considering:
  - 50% discount for eligible gains.
  - Offsetting losses against gains.

---

## Objective

Minimise:

$$
\text{objective} = \text{double\_capital\_gains}
$$

This ensures the lowest possible taxable capital gain under Australian CGT rules.

---

## Notes

- Dates are assumed to be in months for simplicity.
- The model does not include brokerage fees or other transaction costs.
- This approach is useful for investors seeking tax-efficient strategies.

---

### References

- Australian Taxation Office (ATO) guidelines on [Capital Gains Tax](https://www.ato.gov.au/Individuals/Capital-gains-tax/).
