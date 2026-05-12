# Smelt

## Overview

This MiniZinc model describes a **production scheduling** problem that looks like a smelting or mixing plant.
Several customer orders must be produced on a limited number of production lines while sharing limited mineral flow capacity.
The model groups orders by **recipe**, assigns each recipe to a line and a start time, and tries to build a schedule that is both feasible and respectful of soft production rules.

## What the input means

The main data appears to be:

- `m`: number of minerals.
- `f[i]`: available flow rate of mineral `i`.
- `r`: number of recipes.
- `c[k,i]`: amount of mineral `i` consumed while recipe `k` is running.
- `n`: number of orders.
- `t[i]`: recipe used by order `i`.
- `h[i]`, `w[i]`: dimensions of order `i`; the model multiplies them, so this acts like the order's processing size.
- `nl`: number of production lines.
- `p`: number of production rules.
- `typ`, `k1`, `d`, `k2`: soft rules linking pairs of recipes with offsets.

A derived array `duration[j]` computes the total running time of recipe `j` by summing `h[i] * w[i]` over all orders that use that recipe.
So each recipe is treated as one contiguous production block.

## Decision variables

The most important variables are:

- `start[j]`, `end[j]`: start and end time of recipe `j`.
- `line[j]`: production line assigned to recipe `j`.
- `s[i]`, `e[i]`: start and end time of individual order `i`.
- `l[i]`: line used by order `i`.
- `followed[q]`: whether soft production rule `q` is respected.
- `makespan`: finishing time of the whole schedule.
- `violation`: number of production rules that are not followed.

The model forces each order to inherit its recipe's line and to start at an offset within that recipe block.
That means orders of the same recipe are produced back-to-back.

## Constraints

The model enforces three main kinds of constraints:

1. **Line capacity**  
   Each recipe runs on exactly one line, and a line can process at most one recipe at a time.

2. **Mineral flow limits**  
   For each mineral, the total demand of all recipes running at the same time cannot exceed the available flow rate `f[i]`.
   This is modeled with the global `cumulative` constraint.

3. **Production rules**  
   Each rule compares two recipes and may require one to start or finish before/after another with delay `d`.
   There are four encoded rule types, covering bounds on start times or end times.
   These rules are **soft**: the schedule may break them, but then `followed[q]` becomes false.

The model also defines `makespan` as an upper bound on every recipe end time.

## Objective

The model minimizes:

$$
1000 \times \text{violation} + \text{makespan}
$$

So the solver strongly prefers:

1. **fewer broken production rules**, and then
2. **a shorter overall completion time**.

Because the penalty weight is `1000`, rule violations are treated as much more important than small makespan improvements.

## Interpretation notes and uncertainty

This looks like a scheduling benchmark for a smelting plant, but the model does not include a textual problem statement.
A few details are therefore uncertain:

- `h[i]` and `w[i]` are multiplied to form processing time, but their real-world meaning is not explained.
- The exact semantics of the four production rule types are only implied by the inequalities in the model.
- Recipes are scheduled as single uninterrupted blocks, which may be a modeling simplification rather than a physical requirement.

## References

Identifiable references are limited.
The folder metadata shows this benchmark appeared in the **MiniZinc Challenge 2014** instance set.
No paper, author, or original industrial source is cited directly inside the model file.

## Model update summary

Added concise inline comments in smelt.mzn to clarify:

- order/recipe timing and line assignment decision variable semantics,
- resource-flow and production-rule feasibility interpretation,
- weighted minimization intent prioritizing fewer violations then makespan.
