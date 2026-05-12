# Slow Convergence

## What problem is this model expressing?

This MiniZinc file looks like a **synthetic feasibility benchmark** rather than a real-world application model.

It defines two sequences of integer variables, `y[0..n]` and `x[0..n]`, and asks the solver to find **any** values that satisfy a small set of monotonicity and linking constraints. The name **"slow_convergence"** strongly suggests that the point of the model is to test how a solver's propagation reaches a fixpoint, especially when information travels only gradually through chains of inequalities.

So, in beginner-friendly terms, the model is not trying to schedule, pack, or optimize anything. It is mainly asking:

- build a nondecreasing sequence `y` (from index `1` onward),
- build a nondecreasing sequence `x` (from index `1` onward),
- force `y[0]` to be at least `n`, and
- connect the end of the `y` sequence to `x[0]`.

## Input parameter

- `n`: controls the size of the two arrays.

The benchmark instances in `data/` simply provide different values of `n`.

## Decision variables

The model has two arrays of decision variables:

- `y[0..n]` with domain `0..10*n`
- `x[0..n]` with domain `0..10*n`

These are integer variables. The solver chooses their values.

## Main constraints

### 1. `y` is nondecreasing from `y[1]` to `y[n]`

For every `i = 2..n`:

- `y[i-1] <= y[i]`

This means the sequence cannot go down as the index increases.

### 2. Each `y[i]` must stay close enough to `y[0]`

For every `i = 1..n`:

- `y[0] - y[i] <= n - i + 1`

Equivalently:

- `y[i] >= y[0] - (n - i + 1)`

So once `y[0]` is known, it gives a lower bound on every later `y[i]`. The farther right we go, the tighter that lower bound becomes.

### 3. The last `y` value is below `x[0]`

- `y[n] <= x[0]`

This is the only direct link between the `y` array and the `x` array.

### 4. `x[1]..x[n]` is nondecreasing

For all `1 <= i < j <= n`:

- `x[i] <= x[j]`

So the `x` values from index `1` onward are also ordered.

### 5. `y[0]` is at least `n`

- `y[0] >= n`

This is the main starting fact that triggers propagation through the rest of the inequalities.

## Objective

There is **no optimization objective**.

The model uses `solve satisfy;`, so it is a **satisfaction problem**: find any assignment that meets all constraints.

## Why the name "slow convergence"?

Although the model is simple, it is structured so that bound information can propagate only through several linked inequalities. That kind of chain can require repeated propagation rounds before all variable bounds stabilize.

This makes it a plausible benchmark for studying **propagation behavior** rather than modeling a rich application domain.

## Output

If a solution is found, the model prints both arrays:

- `x = ...`
- `y = ...`

## Uncertainty / interpretation notes

- The file contains **no comments** explaining a real-world story.
- I cannot identify a domain interpretation for `x` and `y` from the model alone.
- Because of that, this README interprets the model as an **abstract solver benchmark**.
- The explanation of "slow convergence" is therefore an informed reading of the constraints and filename, not a confirmed statement from the original author.

## References

Identifiable from the repository metadata:

- Included as `slow_convergence` in the MiniZinc benchmark collection.
- `metadata.json` marks it as a satisfaction/combinatorial benchmark and associates challenge instances with **year 2008**.

No paper, competition note, or original author reference is given in the model file itself, so a more precise citation could not be confirmed from the available files.

## Model update summary

Added concise inline comments in `slow_convergence.mzn` to clarify:

- the monotonic chain constraints on `y` and `x`,
- the tightening lower-bound relationship from `y[0]` to later `y[i]`, and
- the linking constraint between `y[n]` and `x[0]`.
