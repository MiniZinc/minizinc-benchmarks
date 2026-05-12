# Still Life (Wastage Formulation)

## Problem Description

The **Still Life** problem asks: how many live cells can you place on an $n \times n$ grid such that the pattern is a _still life_ in [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)?

In Conway's Game of Life, a grid of cells evolves over discrete time steps according to two rules:

- A **live cell** survives to the next generation if it has **2 or 3** live neighbours; otherwise it dies.
- A **dead cell** becomes alive if it has **exactly 3** live neighbours; otherwise it stays dead.

A _still life_ is a pattern that does not change at all — every live cell has 2 or 3 neighbours (so it survives), and no dead cell has exactly 3 live neighbours (so nothing new is born). The optimisation goal is to pack as many live cells as possible into such a stable pattern.

## Model Variables

| Variable         | Type         | Meaning                                                                                                                  |
| ---------------- | ------------ | ------------------------------------------------------------------------------------------------------------------------ |
| `x[i,j]`         | `var 0..1`   | Whether cell $(i,j)$ is alive (1) or dead (0). The grid is $(n+2) \times (n+2)$ with a fixed border of dead cells.       |
| `w[i,j]`         | `var 0..2`   | _Wastage_ at cell $(i,j)$ — an auxiliary measure of how far the cell sits from the stability boundary (explained below). |
| `wastage_sum[i]` | `var int`    | Running cumulative sum of all wastage values up to and including row $i$, used to build the objective incrementally.     |
| `OBJECTIVE`      | `var 0..n*n` | The total number of live cells; this is the value being maximised.                                                       |

## Constraints

**Stability (the `still_life` predicate):** For every interior cell $(i,j)$, the 3×3 neighbourhood centred on it must obey the still-life rules — the centre cell must not die and no dead neighbour may come to life.

**Fixed boundary:** All cells on the outermost ring of the $(n+2) \times (n+2)$ array are fixed to 0, effectively surrounding the $n \times n$ playing area with dead cells.

**Edge density:** Additional constraints restrict how many live cells can appear in any three consecutive positions along the first and last rows/columns, preventing unstable edge patterns.

**Wastage–objective link:** Total wastage and the number of live cells are related by an algebraic identity derived from counting arguments:

$$4 \times \text{OBJECTIVE} = 2n^2 + 4n - \text{wastage\_sum}[n+1]$$

Maximising live cells is therefore equivalent to minimising total wastage.

**Redundant cuts:** The model includes dominance constraints of the form $\text{wastage\_sum}[n+1] \geq \text{wastage\_sum}[i] + f(n,i)$, derived from results in Chu et al. (2012), which tighten the lower bound on remaining wastage and speed up search.

## The Wastage Idea

Rather than reasoning directly about which cells are alive, this formulation introduces the _wastage_ variable for each cell. Intuitively, a cell with high wastage is "wasting" neighbourhood capacity — a live cell surrounded by few neighbours is paying a stability cost that limits how densely the rest of the board can be filled. By bounding and summing wastage across the whole board, the model can derive tight bounds on the maximum possible number of live cells. This _wastage reformulation_ is the key novelty of the model.

## Objective

**Maximise** `OBJECTIVE` — the number of live cells in the $n \times n$ interior.

## Parameters

| Parameter | Meaning                  |
| --------- | ------------------------ |
| `n`       | Side length of the board |

Instance files supply a single value of `n`; typical benchmark instances use $n \in \{9, 10, 11, 12, 13\}$.

## Notes and Uncertainty

- The model does not include a `metadata` problem tag beyond _puzzle / maximisation_, so the original problem source is inferred from the model comments.
- The `still_life` predicate's `s2` and `s3` sub-expressions encode a refined notion of neighbourhood structure whose exact derivation is non-trivial; beginners can treat the predicate as a black-box encoding of the Game of Life stability rules.
- This formulation is also sometimes called the _wastage_ or _density_ formulation to distinguish it from direct cell-counting models.

## References

- Chu, G., Stuckey, P. J., et al. (2012). Referenced directly in the model's redundant-constraint comment.
- Smith, B. M. (2002). _A Dual Graph Translation of a Problem in 'Life'_. CP 2002. — An early influential encoding of the Still Life problem.
- [Conway's Game of Life — Wikipedia](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)

## Model update summary

Added concise inline comments in still-life.mzn to clarify:

- live-cell and wastage decision variable semantics,
- still-life feasibility interpretation under Game of Life rules,
- maximization intent for stable live-cell density.
