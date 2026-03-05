# Protein Design WCSP Reader

This directory contains a generic MiniZinc model (`wcsp.mzn`) that reads a
binary **Weighted Constraint Satisfaction Problem** (WCSP) in the standard format.
It was originally written for the `toulbar2` solver and then adapted to MiniZinc.  
The model is not specific to proteins; it simply interprets a list of unary and
binary cost functions and searches for a complete assignment that minimises total
cost.

## Problem structure

- **Variables**: `num_variables` variables, each with a domain size stored in
  `domains` and a global maximum `max_domain`.
- **Cost functions**: a number of unary (`num_constraints1`) and binary
  (`num_constraints2`) functions.  The data files contain the extension tables
  for these functions, and the model imports them into arrays such as
  `func1x`, `costs1`, `func2x`, `func2y`, `costs2`.
- `top` denotes the special “infinite” cost value used for forbidden tuples.

The model defines decision variables

```minizinc
array[1..num_variables] of var 0..max_domain: p;
``` 
(p holds the chosen value for each variable) and auxiliary variables `ocosts1`,
`ocosts2` for the cost contributed by each unary/binary constraint.

## Objective

The objective is to *minimise* the sum of all constraint costs.  The solver
implements an explicit `solve :: seq_search(...) minimize objective;` strategy
that first decides the variable assignments, then the costs, then the overall
objective.

## Use cases

1. Convert a `.wcsp` file to `.dzn` using the provided `wcsp2dzn.awk` script
   (see comments at the top of the `.mzn`).
2. Run `minizinc wcsp.mzn <datafile>.dzn` to compute the minimum‑cost assignment.

The README is intended to help beginners understand how the format parameters
map to the MiniZinc variables and how the search is structured.