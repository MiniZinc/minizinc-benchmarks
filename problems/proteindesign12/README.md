# ProteinDesign12 (WCSP model)

## What this model is about

This MiniZinc file (`wcsp.mzn`) is a **generic reader/solver model for Binary Weighted CSP (WCSP)** instances.  
A WCSP has:

- variables with finite domains,
- unary and binary cost functions,
- a goal to find a full assignment with **minimum total cost**.

In this format, costs are nonnegative integers, and a special large value `top` is used in WCSP literature to represent effectively forbidden assignments.

## Core data and decision variables

The model expects an instance (usually from a `.dzn` generated from a `.wcsp` file) that defines:

- `num_variables`: number of variables.
- `domains[j]`: domain size for variable `j`.
- Unary-function data (`num_constraints1`, `func1x`, `num_tuples1`, `cum_tuples1`, `costs1`, ...).
- Binary-function data (`num_constraints2`, `func2x`, `func2y`, `num_tuples2`, `cum_tuples2`, `costs2`, ...).

Decision/cost variables in the model:

- `p[j]`: chosen value for variable `j` (declared as `var 0..max_domain`).
- `ocosts1[j]`: realized cost of unary function `j`.
- `ocosts2[j]`: realized cost of binary function `j`.
- `objective`: total cost to minimize.

## How constraints work

1. **Domain restriction**  
   `p[j] < domains[j]` ensures each assignment is within the variable’s valid range.

2. **Unary costs via table constraints**  
   For each unary function, a `table` constraint links `[ocosts1[j], p[func1x[j]]]` to an allowed tuple list extracted from `costs1`.

3. **Binary costs via table constraints**  
   For each binary function, a `table` constraint links `[ocosts2[j], p[func2x[j]], p[func2y[j]]]` to tuples extracted from `costs2`.

So each tuple list acts like an explicit lookup: for every variable-value (or value pair), it specifies the corresponding cost.

## Objective

The model minimizes:

- sum of all unary realized costs, plus
- sum of all binary realized costs.

Formally in the model:
`objective = sum(ocosts1) + sum(ocosts2)` and `solve minimize objective`.

## Notes and uncertainty

- This model is **not specific to protein design logic by itself**; it is a generic WCSP encoding engine used by this benchmark folder.
- The comments warn it assumes **only unary and binary** cost functions, with tuples given in extension (explicit form).
- It declares `objective` in `0..(top-1)`. If an instance’s true sum can reach/exceed `top`, feasibility/meaning depends on how the instance was generated. In many WCSP conventions, `top` is chosen high enough to represent “forbidden” while still supporting optimization safely.
- Variable indices and tuple offsets are driven by `cum_tuples*` arrays; correct interpretation depends on consistent `.dzn` generation.

## References

The model comments point to WCSP format documentation:

- https://mulcyber.toulouse.inra.fr/scm/viewvc.php/trunk/toulbar2/doc/?root=toulbar2
- http://costfunction.org/mobyle/htdocs/portal/help/wcsp.html
- http://graphmod.ics.uci.edu/group/WCSP_file_format

Model author note in comments: Simon de Givry.

## Model update summary

Added concise inline comments in wcsp.mzn to clarify:

- assignment and realized-cost decision variable semantics,
- table-constraint role for unary/binary extension costs,
- minimization intent for total WCSP objective value.
