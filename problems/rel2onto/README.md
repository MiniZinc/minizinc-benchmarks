# rel2onto (MiniZinc model) — Beginner-friendly overview

## What problem is this model solving?

This model combines **two tasks** into one optimization problem:

1. **Attribute matching** (database relation → ontology node)
   - Each attribute must be matched to exactly one allowed ontology node.
   - Matches have costs, and cheaper matches are preferred.
   - The matching is bijective over selected nodes (via `alldifferent`).

2. **Tree extraction in a graph**
   - The model selects a set of nodes and edges that form a connected, acyclic structure (a tree).
   - All matched nodes must appear in that tree.
   - Additional connector nodes can be activated to connect matched nodes.

The final solution balances matching quality and tree cost.

---

## Main inputs (parameters)

- Graph structure:
  - `nbV`, `nbE`, `nodes`, `edges`
  - `adjacent`, `heads`, `tails`, `endpairs`
  - Edge weights `ws`
  - Node subsets:
    - `dnodes`: nodes that can be matched to attributes
    - `cnodes`: connector/upper nodes used to link matched nodes
    - `anodes`: forced-in nodes (comment says these are empty in provided data)
- Matching structure:
  - `nbA`, `atts`
  - `attribute_domains[a]`: allowed ontology nodes for attribute `a`
  - `match_costs[a,i]`: cost of matching attribute `a` to node `i`

---

## Decision variables

- `vs[n]` (bool): whether node `n` is selected in the final tree.
- `es[e]` (bool): whether edge `e` is selected.
- `match[a]` (int): ontology node chosen for attribute `a`.
- `w`: total selected edge weight.
- `wm`: total matching cost.
- `objective = w + wm`.

---

## Core constraints (intuitive view)

- **Tree shape (`treep`)**
  - If an edge is selected, both its endpoints are selected.
  - Selected nodes have parent relationships that enforce connectivity.
  - Acyclicity is enforced (no parent-child 2-cycles).
  - Redundant count constraint: number of selected edges = selected nodes − 1.

- **Matching validity**
  - `match[a]` must come from `attribute_domains[a]`.
  - All matches are different (`alldifferent(match)`).
  - Matched nodes are forced into the selected tree (`vs[match[a]] = true`).

- **Relationship between `dnodes` and matching/tree**
  - A `dnode` is selected iff it is matched by some attribute.
  - Each selected `dnode` has exactly one incident selected edge (acts like a leaf/terminal condition for matched nodes).

---

## Objective

The model **minimizes**:

\[
\texttt{objective} = \texttt{w} + \texttt{wm}
\]

where:

- `w` = sum of selected edge weights (`ws`),
- `wm` = sum of chosen attribute-to-node match costs.

So the solver prefers solutions with both a cheap structural tree and cheap attribute mappings.

---

## What to expect in the output

The model prints:

- `es`: selected edges,
- `vs`: selected nodes,
- `match`: node chosen for each attribute,
- `objective`: total minimized score.

---

## Uncertainty / assumptions

- The comments indicate `anodes` is empty in available data; behavior may differ on other datasets.
- The exact semantics of "ontology direction" are not encoded explicitly in this file (the graph is treated through adjacency + edge selection), so domain interpretation depends on input data conventions.
- The model comment says matching is bijective; in practice this is implemented as `alldifferent(match)` plus domain restrictions, so bijection is with respect to chosen nodes and attributes, not necessarily all ontology nodes.

---

## References identifiable from the model

- Included MiniZinc globals/utilities:
  - `alldifferent.mzn`
  - `arg_sort.mzn`
- Compilation note from file header:
  - `mzn2fzn model.mzn alignment.dzn X.integration.dzn`
- Data split mentioned in comments:
  - `alignment.dzn` for tree-related data
  - `X.integration.dzn` for instance-specific matching data

## Model update summary

Added concise inline comments in rel2onto.mzn to clarify:

- node/edge selection and attribute-match decision variable semantics,
- tree-feasibility and matching-bijection modeling intent,
- minimization intent for combined structure-plus-matching cost.
