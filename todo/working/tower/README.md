# Tower Assignment and Power Planning (MiniZinc)

This model describes a **mobile network planning** problem: decide which tower each handset connects to, and how much transmission power each tower uses, so that users get acceptable signal while tower capacities are respected.

## Problem in plain language

You are given:

- A set of towers and a set of handsets.
- The distance from each handset to each tower.
- A demand value for each handset (how much load it creates).
- A capacity for each tower (how much load it can serve).
- A minimum required signal strength.

The model chooses:

- Which tower each handset should connect to.
- A power level for each tower.

The goal is to make as many handset connections “good” as possible, where a connection is considered good when its chosen tower is not overloaded.

## Key decision variables

- `power[t]`: transmission power level of tower `t` (bounded integer level).
- `tower[h]`: tower selected for handset `h`.
- `overloaded[t]`: true if assigned handset demand at tower `t` exceeds `capacity[t]`.
- `connection_quality[h]`: 1 if handset `h` is connected to a non-overloaded tower, else 0.

## How signal is modeled

Signal loss is distance-based: attenuation is proportional to $1 / d^2$ (inverse-square style decay), scaled and rounded to integers for CP solving.

- `effective_power[p]` gives a nonlinear mapping from power level to emitted power.
- `signal_strength(t,h)` multiplies effective power at tower `t` by attenuation for handset `h`.
- For each tower/handset pair, a helper function computes the **minimum power level** needed to meet the minimum signal threshold.

Then each handset must be assigned to a tower whose selected power is high enough for that handset.

## Constraints (high level)

- **Minimum signal constraint:** the chosen tower for each handset must satisfy the required minimum signal strength.
- **Capacity/overload logic:** overload is detected when total assigned demand at a tower exceeds capacity.
- **Assignment quality:** each handset gets quality 1 if its selected tower is not overloaded.

## Objective

The model maximizes:

- `objective = sum(connection_quality)`

So it tries to maximize the number of handsets connected through non-overloaded towers while still meeting signal requirements.

## Notes and uncertainty

- This explanation is based on the model structure in `tower.mzn` only; no external problem statement was found in this folder.
- The model includes custom helper logic (`arg_max`, `min_transmit_power`) whose intent appears to be selecting towers/power thresholds from boolean conditions; this interpretation is inferred from code patterns.
- Some implementation details (e.g., scaling/rounding choices and nonlinear power curve) may represent modeling trade-offs rather than physical radio realism.

## References identifiable from the model

- MiniZinc global library include: `globals.mzn`
- MiniZinc cardinality include: `global_cardinality_low_up.mzn`
- The domain idea appears related to wireless tower assignment with power control and capacity constraints.