# Propagation Stress (MiniZinc)

## What this model is about

This model is a **constraint propagation stress test**. It is designed to create many related inequality constraints so that a solver has to do a lot of bound propagation work.

The top comment says the instance is **unsatisfiable** (“Problem is unsatisfiable”). Intuitively, the constraints force a chain of nondecreasing values, then add two linking constraints between the `x` and `y` arrays that cannot all hold together.

## Inputs (parameters)

- `k`: number of times around the loop (used to scale variable domains).
- `n`: number of loop changes / `y`-chain length.
- `m`: controls the `x`-chain size (`m^2` propagators per loop change, per comment).

All decision variables are bounded in `0..k*n`.

## Decision variables

- `y[0..n]`: integer variables.
- `x[0..m]`: integer variables.

Both are declared as `var 0..k*n`.

## Constraints, in plain language

1. **Monotone chain on `y`**  
   For `i = 2..n`: `y[i-1] <= y[i]`.

2. **Upper-distance constraints from `y[0]`**  
   For `i = 1..n`: `y[0] - y[i] <= n - i + 1`.  
   This limits how far each `y[i]` can be below `y[0]`.

3. **Link from end of `y` to start of `x`**  
   `y[n] <= x[0]`.

4. **Monotone chain on `x`**  
   For all `0 <= i < j <= m`: `x[i] <= x[j]`.

5. **Closing link back to `y[0]`**  
   `x[m] <= y[0] - 2`.

Together, (3) + monotonicity imply `y[n] <= x[m]`, while (5) implies `x[m] <= y[0]-2`, so `y[n] <= y[0]-2`. Combined with the `y` constraints, this creates a contradiction for the intended benchmark settings, yielding no solution.

## Objective

There is **no optimization objective**. The model uses:

- `solve satisfy;`

So this is a pure feasibility/unsatisfiability test.

## Notes on uncertainty

- The model comments state unsatisfiable behavior, but strict unsatisfiability still depends on the chosen parameter values (`k`, `n`, `m`) being valid benchmark settings.
- The exact benchmark provenance (paper/competition source) is not stated directly in the file.

## Possible references

Identifiable from the model itself:

- In-file label: “propagation stress”.
- Repository context: MiniZinc benchmark collection (`minizinc-benchmarks`).

No explicit external publication or author reference is embedded in `prop_stress.mzn`.

## Model update summary

Added concise inline comments in `prop_stress.mzn` to clarify:

- the monotonic propagation chains on `y` and `x`,
- the tightening relation from `y[0]` to later `y[i]`,
- the linking constraint between arrays, and
- how the final inequality closes the contradiction used in this UNSAT stress benchmark.
