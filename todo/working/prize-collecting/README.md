# Prize-Collecting (MiniZinc Model Guide)

This model describes a **prize-collecting path/tour-style optimization** problem on `n` nodes.
Each node can be either included in a route or left out. If a node is included, it points to a successor node, and the model earns a prize based on that choice.
The goal is to maximize the total collected prize.

## What the input means

- `n`: number of nodes.
- `p[i,j]` for `i in 1..n`, `j in 0..n`: prize gained when node `i` chooses successor `j`.
  - `j = 0` is used as a special value (node unused / no successor).
  - `j >= 1` refers to an actual node.

The model also computes helper bounds (`min_p`, `max_p`, `max_obj`) to define variable domains safely.

## Decision variables

- `pos[i] in 0..n`: position of node `i` in the path.
  - `0` means node `i` is not used.
- `next[i] in 0..n`: successor of node `i`.
  - `0` means unused.
  - positive values indicate a successor node.
- `prize[i]`: prize contribution of node `i`.
- `objective`: total prize across all nodes.

## Core constraints (plain language)

1. **Start anchor**: `pos[1] = 1`.
   - Node 1 is forced to be in position 1.

2. **Used vs unused consistency**:
   - `pos[i] > 0 <-> next[i] > 0`.
   - A node is used exactly when it has a nonzero successor.

3. **At most one predecessor per node**:
   - For each node `i`, at most one `k` can satisfy `next[k] = i`.

4. **Position progression**:
   - If `next[i] > 1`, then `pos[next[i]] = pos[i] + 1`.
   - Intuition: following a successor should move one step forward in position.

5. **Prize definition**:
   - `prize[i] = p[i, next[i]]`.

6. **Total score**:
   - `objective = sum(prize[i])`.

## Objective

- **Maximize** `objective`.
- So the solver chooses which nodes to use and how to connect them (via `next`) to get the largest total prize.

## Important uncertainty / modeling notes

- The model looks like a path/tour encoding, but it does **not explicitly enforce** some properties a beginner might expect (for example, a strict “exactly one outgoing/incoming for every used node” tour structure, or an all-different constraint on used positions).
- The condition `next[i] > 1 -> ...` is unusual because it excludes the case `next[i] = 1` from position-propagation; this may be intentional (special handling of node 1) or may reflect a modeling simplification.
- Because of these details, the exact combinatorial structure is best described as a **prize-maximizing successor/position assignment with partial path semantics**, rather than a guaranteed classical TSP tour.

## References

- Problem name from metadata: **prize-collecting**.
- Metadata indicates this benchmark appears in **MiniZinc Challenge 2011** and **MiniZinc Challenge 2016** instance sets.
- No explicit external publication or URL is provided in the local metadata/model files.
