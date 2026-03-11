# Ghoulomb

## Problem Description

The **Ghoulomb** problem is a deliberately tricky variant of the classic **Golomb Ruler** problem, designed as a benchmark to stress-test constraint solvers.

### Background: The Golomb Ruler

A [Golomb ruler](https://en.wikipedia.org/wiki/Golomb_ruler) is a set of non-negative integer _marks_ placed on a ruler such that **all pairwise distances between marks are distinct**. For example, a ruler with marks at positions `{0, 1, 3}` is a valid Golomb ruler because the distances are 1, 2, and 3 — all different.

The classic optimization goal is to find the **shortest** Golomb ruler with a given number of marks (i.e., minimize the position of the last mark).

### The "Ghoulomb" Twists

This model intentionally introduces several complications that make it harder for solvers to handle efficiently:

1. **Three rulers, one objective.** Three independent Golomb rulers are constructed (with sizes `m1`, `m2`, and `m3` marks respectively), but **only the middle ruler (ruler 2) is minimized**. The first and third rulers are essentially "decoys" that add redundant work to the search.

2. **Non-idiomatic constraint.** Instead of using the natural `all_different` constraint to enforce that all pairwise distances are distinct, the model uses a **cumulative scheduling constraint** as an equivalent but less efficient substitute. This simulates a modeler who is unaware of the best constraint to use, and tests whether a solver can still propagate effectively.

3. **Inflated resource capacity.** The cumulative constraint uses a resource capacity and task requirements chosen so that the problem remains _disjunctive_ (tasks still cannot overlap), but the numbers are unnecessarily large. This further reduces propagation efficiency.

## Parameters

| Parameter | Description                                                 |
| --------- | ----------------------------------------------------------- |
| `m1`      | Number of marks on Golomb ruler 1                           |
| `m2`      | Number of marks on Golomb ruler 2 (the one being optimized) |
| `m3`      | Number of marks on Golomb ruler 3                           |

Instance files are named using the pattern `m1-m2-m3`, e.g. `4-9-10.json` sets `m1=4`, `m2=9`, `m3=10`.

## Variables

| Variable       | Description                                                            |
| -------------- | ---------------------------------------------------------------------- |
| `mark1[1..m1]` | Integer positions of marks on ruler 1; domain `0..m1*m1`               |
| `mark2[1..m2]` | Integer positions of marks on ruler 2; domain `0..m2*m2`               |
| `mark3[1..m3]` | Integer positions of marks on ruler 3; domain `0..m3*m3`               |
| `differences1` | All pairwise distances between marks on ruler 1                        |
| `differences2` | All pairwise distances between marks on ruler 2                        |
| `differences3` | All pairwise distances between marks on ruler 3                        |
| `objective`    | The position of the last mark on ruler 2 (i.e., the length of ruler 2) |

For each ruler, the marks are ordered (`mark[i] < mark[i+1]`), the first mark is fixed at 0, and all pairwise distances must be distinct.

A symmetry-breaking constraint is also applied: the smallest pairwise distance must be less than the largest, halving the search space by eliminating mirror-image solutions.

## Objective

**Minimize** `objective = mark2[m2]`, the length (span) of ruler 2.

## Instances

This problem appeared in the **MiniZinc Challenge** in [2010](https://www.minizinc.org/challenge2010/results2010.html) and [2013](https://www.minizinc.org/challenge2013/results2013.html).

## References

- Golomb, S. W. (1972). _How to Number a Graph_. Graph Theory and Computing, Academic Press.
- MiniZinc Challenge 2010: <https://www.minizinc.org/challenge2010/>
- MiniZinc Challenge 2013: <https://www.minizinc.org/challenge2013/>
- Wikipedia: [Golomb ruler](https://en.wikipedia.org/wiki/Golomb_ruler)
