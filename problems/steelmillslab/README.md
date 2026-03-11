# Steel Mill Slab

## Problem description

This model represents a **steel mill slab design** problem.
A steel mill must place customer orders onto a limited number of steel slabs before production.

Each order has:

- a **size** (`ordSize`), meaning how much steel it needs,
- a **colour** (`ordCol`), which usually stands for a production class such as grade or processing route.

Each slab can be chosen only from a fixed set of allowed slab capacities (`sizes`).
The goal is to group orders onto slabs so that:

1. the total size assigned to a slab fits within one available slab capacity, and
2. each slab contains orders of **at most two colours**.

If a slab is not perfectly filled, some steel is wasted. The model tries to minimize that waste.

---

## Main decision variables

| Variable    | Meaning                                     |
| ----------- | ------------------------------------------- |
| `assign[o]` | Which slab order `o` is assigned to         |
| `loads[s]`  | Total size loaded onto slab `s`             |
| `objective` | Total unused capacity across all used slabs |

There are at most `nbOrders` potential slabs, which is a safe upper bound: in the worst case, every order could go on its own slab.

---

## Key constraints

The model enforces the following ideas:

1. **Every order is assigned to one slab**  
   The array `assign` chooses a slab index for each order.

2. **Slab load is computed from assigned orders**  
   The derived array `loads` uses `bin_packing_load(...)` to sum the sizes of all orders placed on each slab.

3. **At most two colours per slab**  
   For each slab, the model counts how many distinct colours appear among its assigned orders and requires that number to be at most 2.

4. **Unused capacity is based on the next feasible slab size**  
   The array `frees[l]` precomputes the smallest possible leftover space if a slab carries load `l`. For example, if the allowed capacities are 10 and 15, then a load of 12 would leave 3 units free.

5. **Some symmetry is removed**  
   The model also adds symmetry-breaking constraints so equivalent slab permutations are less likely to be explored. These do not change the real problem, only its representation.

---

## Objective

Yes — this is an **optimization** model.
It minimizes the total unused slab capacity:

$$
\min \sum_{s=1}^{nbSlabs} frees[loads[s]]
$$

So the solver prefers packings that fit orders tightly into the available slab sizes while still respecting the colour limit.

---

## Beginner intuition

You can think of this as a packing problem with an extra compatibility rule:

- **sizes** say how big the available bins are,
- **orders** are the items to place,
- **colours** restrict which items may share a bin,
- the objective penalizes wasted space.

A good solution uses few slabs effectively and leaves as little leftover capacity as possible.

---

## Uncertainty and assumptions

Some interpretation is inferred from the model structure rather than stated explicitly in comments.
In particular:

- the exact real-world meaning of "colour" is not explained in the file,
- the model assumes slab capacities come from the fixed set `sizes`,
- the model measures waste only as **unused capacity**, not other production costs such as setup time or sequence effects,
- the original source of the benchmark is not cited directly inside the model.

So this README describes the implemented optimization model faithfully, but some business context may come from the original benchmark source rather than the MiniZinc file itself.

---

## References and identifiable context

From the repository metadata, this model appears as the `steelmillslab` benchmark and includes instances used in the **MiniZinc Challenge 2017** and **2019**.

The problem name strongly suggests the well-known **Steel Mill Slab Design** benchmark, but the exact paper or original industrial source is **not explicitly referenced in the model file**, so that identification should be treated as likely rather than certain.
