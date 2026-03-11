# Products and Shelves (MiniZinc) — Beginner Guide

## What problem is being solved?

This model packs products into shelves in a warehouse.

- Each **product** is a 3D box with fixed `Length`, `Width`, and `Height`.
- Each **shelf** is also a 3D box with fixed dimensions.
- Products **cannot be rotated**.
- The model must place all items so they do not overlap and stay inside shelf bounds.
- The goal is to use as few shelves as possible.

In optimization terms, this is a constrained 3D packing / assignment problem with a minimization objective.

## Main input data (parameters)

The model expects:

- `Product`: product types.
- `shelves[Dimension]`: shelf size in each dimension.
- `product_size[Product, Dimension]`: size of each product type.
- `nr_shelves`: number of available shelves.
- `nr_products[Product]`: how many units of each product type exist.

Derived sets include:

- `Shelf = S(1..nr_shelves)`
- `Item = I(1..sum(nr_products))` (every physical unit/item)
- `product[Item]` mapping each item to its product type.

## Decision variables (what the solver chooses)

- `item_shelving[it]`: which shelf item `it` is assigned to.
- `item_shelve_placement[it, s, d]`: start coordinate of item `it` on shelf `s` in dimension `d`.
- `item_shelve_size[it, s, d]`: effective size of item `it` on shelf `s` in dimension `d`.
  - If item `it` is on shelf `s`, this equals its product size.
  - Otherwise it is `0` (so non-assigned items do not consume space on that shelf).
- `last_loaded_shelf`: highest-index shelf that has at least one assigned item.
- `objective = enum2int(last_loaded_shelf)`.

## Core constraints (high level)

1. **Activation-by-assignment**  
   Item size is real only on its selected shelf; size is zero on all other shelves.

2. **No overlap on each shelf**  
   Uses global constraint `diffn_nonstrict_k(...)` so items on the same shelf do not occupy overlapping volume.

3. **Inside shelf bounds**  
   For each dimension: `placement + size <= shelf_size`.

4. **Symmetry breaking**  
   Extra constraints reduce equivalent duplicate solutions (for shelf order and identical products) to speed solving. They do not change the set of valid packings.

## Objective

Minimize the number of used shelves:

- Because shelves are forced to be used from low index to high index, minimizing `last_loaded_shelf` is equivalent to minimizing how many shelves are used.

## Notes and uncertainty

- The model header states it was authored by **Danyal Mirza (Ericsson)** and later modified by MiniZinc Challenge organizers (adding integer `objective`).
- The exact original industrial context (for example, whether additional real-world constraints existed outside this `.mzn`) is **not fully specified** in the model file.
- This explanation is based on the visible MiniZinc model and metadata in this repository.

## References

- Model source header in `product-and-shelves.mzn` (author and license).
- Repository metadata for this benchmark (`metadata.json`), including MiniZinc Challenge 2025 instance list.
- Included MiniZinc global constraints: `diffn_nonstrict_k`, `increasing`, `lex_chain_lesseq`, `seq_precede_chain`.
