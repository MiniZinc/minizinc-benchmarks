# MiniZinc Model: Products on Shelves

## **Overview**

This MiniZinc model solves a **warehouse optimisation problem** where a set of products must be placed on shelves in a way that minimises the number of shelves used. Both products and shelves are represented as **3D boxes** with fixed dimensions (length, width, height). Products cannot be rotated, and shelves have limited capacity in each dimension.

---

## **Problem Description**

- **Goal:** Arrange all products on available shelves such that:

  - Products do not overlap.
  - Each product fits within the dimensions of its assigned shelf.
  - The total number of shelves used is minimised.

- **Constraints:**
  - Products and shelves are axis-aligned (no rotation allowed).
  - Each shelf has fixed dimensions.
  - Products must be placed without overlapping.
  - Symmetry-breaking constraints are applied to reduce redundant solutions.

---

## **Parameters**

- `enum Dimension = {Length, Width, Height}`  
  Represents the three dimensions of products and shelves.
- `enum Product`  
  Set of product types.
- `array[Dimension] of int: shelves`  
  Dimensions of each shelf.
- `array[Product, Dimension] of int: product_size`  
  Dimensions of each product type.
- `int: nr_shelves`  
  Total number of shelves available.
- `array[Product] of int: nr_products`  
  Number of units for each product type.

Derived:

- `enum Shelf = S(1..nr_shelves)`  
  Identifiers for shelves.
- `enum Item = I(1..sum(nr_products))`  
  Individual items (all products combined).
- `array[Item] of Product: product`  
  Maps each item to its product type.

---

## **Decision Variables**

- `array[Item, Shelf, Dimension] of var 0..max(product_size): item_shelve_size`  
  Size of each item on a shelf (or `[0,0,0]` if not placed there).
- `array[Item] of var Shelf: item_shelving`  
  Shelf assigned to each item.
- `array[Item, Shelf, Dimension] of var 0..max(shelves): item_shelve_placement`  
  Starting position of each item on its shelf.
- `var Shelf: last_loaded_shelf`  
  The highest-indexed shelf that contains at least one product.
- `var int: objective`  
  Minimisation target: number of shelves used.

---

## **Constraints**

1. **Size Assignment:**  
   If an item is on a shelf, assign its size; otherwise, set size to zero.
2. **Non-overlapping:**  
   Use `diffn_nonstrict_k` to ensure items on the same shelf do not overlap.
3. **Shelf Boundaries:**  
   Each item must fit within the shelf dimensions.
4. **Symmetry Breaking:**
   - Shelves filled in ascending order.
   - Items of the same product placed in increasing order.
   - Lexicographic ordering for placement of identical products.

---

## **Objective**

Minimise:

```minizinc
objective = enum2int(last_loaded_shelf);
```

This ensures the smallest number of shelves is used.

---

## **Applications**

- Warehouse space optimisation.
- Inventory management.
- Packing and logistics planning.

---

## **References**

- Based on common bin-packing and 3D placement problems in operations research.
- Related literature: N. Beldiceanu et al., _Global Constraints for Packing Problems_.

---
