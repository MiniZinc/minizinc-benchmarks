# Fast Food Depot Placement Model

## Overview

This MiniZinc model chooses locations for a fixed number of depots that will serve a set of fast-food restaurants placed along a road. Each restaurant has a known kilometre position, and the goal is to place the depots so that restaurants are as close as possible to their nearest depot.

At a high level, this is a **facility location** problem on a straight line. More specifically, it is very close to a **1-dimensional p-median** problem: select `p` facility locations to minimise the total distance from customers to their nearest facility.

## Problem Being Solved

The input describes:

- a set of restaurants,
- the name of each restaurant,
- the kilometre marker where each restaurant lies,
- and the number of depots that may be opened.

The model must decide where to place the depots. A restaurant is considered served by the depot that is nearest to it. The total cost is the sum of these nearest distances over all restaurants.

This means the model tries to find a small set of depot positions that gives good overall coverage of the restaurants.

## Main Inputs

- `nr`: number of restaurants.
- `Restaurant`: index set for the restaurants.
- `name[r]`: name of restaurant `r`.
- `k[r]`: kilometre position of restaurant `r`.
- `number_of_depots`: how many depots must be placed.

The model also builds some helper sets:

- `ks`: the set of distinct kilometre positions used by restaurants.
- `maxdist`: the largest kilometre value.
- `first`: one representative restaurant for each distinct position, used only for cleaner output.

## Decision Variables

- `p[d]`: the position of depot `d`.

Each depot position is a decision variable. The model restricts each depot to be placed at one of the restaurant kilometre positions already present in the data.

- `obj`: the total distance from every restaurant to its nearest depot.

This is the optimisation value that the model minimises.

## How the Model Works

The model enforces two main structural rules:

1. **Depots must be placed at existing restaurant positions.**
   This means the solution chooses from the set of observed kilometre markers rather than any arbitrary point on the road.

2. **Depot positions are strictly increasing.**
   This simply keeps the depots ordered from left to right and avoids duplicate or symmetric solutions.

For each restaurant, the model computes the distance to every depot and keeps the smallest one. The total objective is the sum of these smallest distances.

## Objective

The objective is:

$$
\text{minimise } \sum_{r \in Restaurant} \min_{d \in Depot} |p[d] - k[r]|
$$

In plain language:

- find the nearest depot for each restaurant,
- measure how far away it is,
- add these distances for all restaurants,
- and make that total as small as possible.

A smaller objective means the depot network is, overall, closer to the restaurants.

## Output

The model prints:

- the chosen depot positions,
- the final objective value,
- and a simple list of depot facts of the form `depot(name,position)`.

When several restaurants share the same kilometre position, the output uses one representative restaurant name for that position.

## Notes and Interpretation

This model is easy to understand as a planning problem for supply, distribution, or service coverage along a highway. The restaurant names in the sample data appear to be service-area names, which suggests a road-based logistics setting.

One detail is not explicitly documented in the model: whether a “depot” should be interpreted as a warehouse, distribution centre, or another kind of supply point. The mathematics is clear, but if a more domain-specific explanation is needed, another expert may need to confirm the original application context.

## References

- The model matches the classical **p-median / facility location** idea on a line.
- It appears in this benchmark collection as the **fast-food** MiniZinc challenge model.
- No explicit paper or source citation is included in the model file or metadata, so the exact original publication could not be confirmed from the available files.

## Model update summary

Added concise inline comments in `fastfood.mzn` to clarify:

- why one representative restaurant per position is used in output,
- why depot positions are restricted to restaurant positions,
- why depot ordering is enforced (symmetry breaking), and
- how objective bounds and the nearest-depot objective expression are intended to guide search and readability.
