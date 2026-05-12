# Sparse Minimal Decision Sets (MiniZinc Model)

## What problem is this model solving?

This model builds a **small, interpretable rule-based classifier** for binary data.  
Each training item has binary feature values (`0/1`), including one feature that is the true class label (`class`).

The model tries to choose a compact set of decision nodes that:

1. classify as many items correctly as possible, and
2. use as few nodes as possible.

So it balances **accuracy** and **simplicity**.

---

## High-level idea

The model has a fixed maximum number of node slots (`n`). Each slot can become:

- a **test node** (check one feature against true/false),
- a **leaf node** (predict class true/false), or
- **unused**.

For each item, the model tracks whether that item is still “valid” at each node position (meaning it is still consistent with the tests so far). If an item reaches a leaf, the leaf prediction should match the item’s class; otherwise the item may be marked as misclassified.

A coverage rule ensures every item is either:

- covered by at least one valid leaf, or
- explicitly marked as misclassified.

---

## Inputs

- `n`: maximum number of node positions.
- `FEATURE`: enum of all features.
- `class`: one distinguished feature in `FEATURE` used as the ground-truth label.
- `I`: number of items.
- `db[ITEM, FEATURE]` in `0..1`: binary dataset.
- `Lambda = I div 20`: penalty weight used to trade model size against errors.

---

## Decision variables (main modeling choices)

- `feat[j]`: which feature node `j` uses.
  - normal feature => test node,
  - `class` => leaf node,
  - `dummy` => unused node.
- `sign[j]`: boolean meaning of node `j`.
  - at test nodes, this is the required feature value,
  - at leaf nodes, this is the predicted class value.
- `valid[j,i]`: item `i` is still valid at node `j`.
- `m[i]`: item `i` is allowed to be misclassified.

Auxiliary:

- `leaf[j]`: true when `feat[j] = class`.
- `unused[j]`: true when `feat[j] = dummy`.
- `k`: number of used nodes.

---

## Objective

The model minimizes:

`objective = misclassified + Lambda * k`

where:

- `misclassified = sum(m)` is the number of misclassified items,
- `k` is the number of used nodes.

Interpretation: each extra node has a cost of `Lambda` error units. A larger `Lambda` pushes toward smaller models; a smaller `Lambda` pushes toward better fit.

---

## Notes and limitations

- This model assumes **binary features** and a **binary class label** stored as one of those features.
- Node structure is constrained to keep used and unused regions consistent and avoid invalid layouts.
- There are commented-out symmetry-breaking constraints that could reduce equivalent solutions.

---

## Literature context (best-effort)

The formulation is in the style of sparse, interpretable rule/decision-set learning. I could not confidently identify the exact paper source from this file alone.

Related background you may want to check:

- Lakkaraju, Bach, and Leskovec (KDD 2016), _Interpretable Decision Sets: A Joint Framework for Description and Prediction_.
- Malioutov and Meel (2018), _Minds: Multi-Value Rule Sets from Data_ (and related sparse rule-learning work).

If exact attribution is needed, an additional repository history or publication link would help an expert confirm provenance.

## Model update summary

Added concise inline comments in sparse_mds.mzn to clarify:

- node feature/sign decision variable semantics,
- objective trade-off between errors and model size,
- minimization interpretation for sparse decision sets.
