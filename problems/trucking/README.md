# Trucking (MiniZinc model) — Beginner-friendly explanation

You are given:
- `T` time periods,
- `N` trucks,
- each truck’s load capacity (`Loads[i]`) and cost per use (`Cost[i]`),
- demand per period (`Demand[t]`).

The model decides, for each truck and each time period, whether the truck is used (`1`) or not (`0`).

---

## Main decision variables
- `x[i,t]` (binary):
  - `1` if truck `i` is used in period `t`
  - `0` otherwise
- `total_cost` (integer): total cost of all selected truck usages

So the key decision is the binary usage matrix `x` of size `N × T`.

---

## Core constraints (plain language)
1. **Demand must be covered every period**
   - For each time period `t`, the total transported load from selected trucks must be at least `Demand[t]`.
   - Formula idea: sum of `Loads[i] * x[i,t]` over all trucks `i` is `>= Demand[t]`.

2. **Special spacing rule for `Truck1`**
   - In any 3 consecutive periods, `Truck1` can appear at most once.
   - This enforces rest/cooldown-like spacing for that truck.

3. **Special spacing rule for `Truck2`**
   - In any 2 consecutive periods, `Truck2` can appear at most once.
   - This is a slightly weaker spacing than the `Truck1` rule.

---

## Objective
The model **minimizes total cost**:
- `total_cost = sum over all trucks and periods of Cost[i] * x[i,t]`
- Solver goal: choose feasible truck usage with the smallest `total_cost`.

---

## Input data you need
To run this model, data must provide at least:
- `T`, `N`
- truck indices for `Truck1`, `Truck2` (as values in `1..N`)
- arrays `Demand[1..T]`, `Cost[1..N]`, `Loads[1..N]`

---

## Output produced by the model
The model prints:
- total cost (`total_cost`)
- a readable table of `x[i,t]`
- an `array2d(...)` representation of `x` for reuse

---

## Uncertainty / assumptions to be aware of
- The comments suggest a practical trucking scheduling story, but the exact business interpretation (e.g., why only `Truck1` and `Truck2` have spacing rules) is not fully documented in the model.
- Costs are modeled per truck-use per period; there are no explicit fixed startup costs, travel times, route limits, or fleet availability constraints beyond the binary usage and the two special truck rules.
- Demand is treated as a minimum required load each period (over-supply is allowed because constraint is `>=`).

---

## Identifiable references
From the model header comments:
- Author: **Jakob Puchinger**
- Date: **December 2007**
- Note: “Original model comes from Peters Student Tim” (as written in source comment)

No external paper/report citation is explicitly provided in the model file.

## Model update summary

Added concise inline comments in trucking.mzn to clarify:

- truck-usage decision variable semantics,
- demand-cover and spacing feasibility constraints,
- objective intent as minimizing total truck usage cost.
