# Linear-to-Program (l2p)

## Problem Description

This model solves a **program synthesis** problem: given a target linear combination of input variables, find the _shortest possible program_ that computes it using only two operations:

- **Binary addition** (`a + b`)
- **Unary negation** (`-a`)

For example, to compute `-2·p0 + -1·p1 + 2·p2`, a valid (shortest) synthesised program might be:

```
x3 = p0 + p0
x4 = p1 + x3
x5 = p2 + p2
x6 = - x4
x7 = x5 + x6
return x7
```

The model is part of a **counter-example guided synthesis (CEGIS)** loop. In such a loop, a program is proposed, then a verifier checks whether it is correct on all possible inputs. If not, a failing input (counter-example) is fed back to refine the search. This model handles only the _program generation_ step; the counter-example generation is external.

To keep the problem tractable, correctness is checked against a finite set of concrete input/output _examples_ rather than all possible inputs. New examples are added whenever the current program is found to be wrong.

## Parameters

| Parameter | Meaning                                                                         |
| --------- | ------------------------------------------------------------------------------- |
| `N`       | Maximum number of lines (operations) in the synthesised program                 |
| `M`       | Number of input parameters (`p0`, `p1`, ..., `p(M-1)`)                          |
| `coef`    | Integer coefficients of the target linear combination (one per input parameter) |
| `Np`      | Number of addition operations available in the program                          |
| `Smax`    | Number of test examples used to validate the program                            |
| `RP`      | Concrete input values for each example (a `Smax × M` array)                     |

The remaining `N - Np` operations are unary negations.

## Decision Variables

| Variable    | Meaning                                                                                                                          |
| ----------- | -------------------------------------------------------------------------------------------------------------------------------- |
| `line_o[r]` | The line number (position in the program) to which operation `r` is assigned                                                     |
| `line_i[j]` | The line number of the input fed into slot `j` of an operation (either an original input `p_k` or the output of a previous line) |
| `objective` | The line number whose output is returned as the final answer — **this is the value being minimised**                             |
| `x_o[s, r]` | The numeric value produced by operation `r` when run on example `s`                                                              |
| `x_i[s, j]` | The numeric value fed into input slot `j` when run on example `s`                                                                |

## Constraints

- **All operations are placed on distinct lines** (`alldifferent` on `line_o`).
- **Data-flow ordering**: every input to an operation must come from an earlier line (no cycles, no forward references).
- **Correctness on examples**: for each test example, the program must produce the correct target value.
- **Symmetry breaking**: addition operations (which are commutative and interchangeable with each other) are ordered to reduce equivalent solutions.

## Objective

Minimise `objective` — the line number of the final `return` statement. A smaller line number means fewer operations are used, so the model finds the **shortest correct program**.

## Instance Details

Instances vary in the number of input parameters (`M`), the target coefficients (`coef`), the budget of operations (`N`, `Np`), and the number of examples (`Smax`). The benchmark instances were used in the **MiniZinc Challenge 2013**.

## Author

Jean-Noël Monette, Uppsala University.

## Notes

The model relies on the CEGIS framework for completeness: because correctness is only verified against a finite sample of examples, a program that passes all examples but is globally wrong would require additional examples to be added and the model re-solved. This file models only the synthesis (program generation) subproblem.

## References

- MiniZinc Challenge 2013. [https://www.minizinc.org/challenge2013/](https://www.minizinc.org/challenge2013/)
- Solar-Lezama, A. (2008). _Program Synthesis by Sketching_. PhD thesis, UC Berkeley. (Background on CEGIS-based synthesis.)
