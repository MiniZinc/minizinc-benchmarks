# Australian Capital Gains Tax Optimisation

## Overview

This model optimises **Australian Capital Gains Tax (CGT)** liability for a portfolio of stock trades. When an investor buys and later sells shares, each sale may produce either a capital gain (sold for more than was paid) or a capital loss (sold for less). Under Australian tax law, gains are taxable, but a **50% discount** applies to gains on assets held for 12 months or more. Losses can be used to offset gains.

Because shares of the same stock are **fungible** (individual units are indistinguishable), the investor has a choice: when selling units, they can decide which previously purchased units to treat as the ones being sold. Different choices lead to different tax outcomes. This model finds the assignment that **minimises the total taxable capital gain**.

---

## Problem Description

An investor holds a portfolio of stocks and makes a series of buy and sell trades over time. Each trade records:

- The **date** of the trade (represented as an integer, e.g. months since a reference point)
- Whether it is a **buy** or **sell**
- The **stock** being traded
- The number of **units** bought or sold
- The **price per unit**

At tax time, every sold unit must be matched back to exactly one previously purchased unit of the same stock. The difference in price determines whether that pair produces a gain or a loss, and how long the unit was held determines whether the gain qualifies for the discount.

The model searches over all valid matchings of sold units to bought units and finds the one that results in the smallest tax liability.

---

## Parameters

| Parameter | Description                                                                                                   |
| --------- | ------------------------------------------------------------------------------------------------------------- |
| `STOCK`   | The set of stocks in the portfolio (e.g. `{A, B, C}`)                                                         |
| `trades`  | An array of trade records, each with a date, direction (Buy/Sell), stock, number of units, and price per unit |

From the trades, the model automatically expands multi-unit trades into individual unit records:

- `unit_buys`: One record per individual unit purchased, with its date, stock, and price
- `unit_sells`: One record per individual unit sold, with its date, stock, and price

---

## Decision Variable

| Variable    | Description                                                                |
| ----------- | -------------------------------------------------------------------------- |
| `origin[u]` | For each sold unit `u`, the index of the bought unit that it is matched to |

This is the core of the model: deciding which buy lot each sold unit "came from".

---

## Constraints

1. **No double-selling**: Each bought unit can only be matched to one sold unit (`all_different` on `origin`).
2. **Buy before sell**: The buy date of the matched unit must be strictly earlier than the sell date.
3. **Symmetry breaking**: Units of the same stock sold in the same trade at the same price are interchangeable, so their origins are forced into increasing order to avoid exploring equivalent duplicate solutions.

---

## Objective

The model minimises taxable capital gains, computed as follows:

- **Discountable gains**: Gains on units held for **12 or more months** (eligible for 50% CGT discount).
- **Undiscountable gains**: Gains on units held for **fewer than 12 months** (no discount applies).
- **Capital losses**: Losses on any sold unit (regardless of holding period). Losses first offset undiscountable gains, then discountable gains.

The final objective is `double_capital_gains`, which represents twice the actual taxable gain. Doubling avoids the need for fractional arithmetic when applying the 50% discount. Minimising this value is equivalent to minimising the actual tax liability.

The loss-offsetting logic follows Australian Tax Office (ATO) rules: capital losses are applied first against undiscountable gains (to maximise the benefit of the discount on any remaining gains).

---

## Notes

- Dates in the input data are represented as **integer months** rather than calendar dates.
- Prices are represented as **integers** (e.g. cents), so there are no floating-point values in the model.
- This problem was contributed to the MiniZinc Challenge 2025 and was written by Jason Nguyen at Monash University.
- No academic paper is known to be associated with this model; it is an original contribution based on real Australian tax rules. If you are aware of prior related work in the constraint programming or operations research literature, please raise an issue.

## Model update summary

Added concise inline comments in cgt.mzn to clarify:

- unit-level expansion from trade records into unit_buys and unit_sells,
- the matching decision variable origin and its role in buy/sell pairing,
- integer-only taxable-gain computation via double_capital_gains.
