# Compression

## Problem Description

This model solves an **optimal data compression** problem. Given a sequence of bytes (the input text), the goal is to find the smallest possible encoding of that text by:

1. **Identifying recurring byte patterns** — substrings of the original text that appear one or more times.
2. **Building a binary prefix code tree** — assigning a variable-length binary code to each pattern, so that more frequently used patterns receive shorter codes (similar in spirit to Huffman coding).
3. **Minimizing the total encoded size** — the number of bits needed to store both the pattern dictionary and the encoded text together.

The approach combines two classical compression ideas: **dictionary-based compression** (reusing repeated substrings) and **variable-length prefix coding** (shorter codes for more common patterns).

## Input Parameters

| Parameter         | Description                                                       |
| ----------------- | ----------------------------------------------------------------- |
| `max_pattern`     | The maximum number of distinct patterns allowed in the dictionary |
| `max_pattern_len` | The maximum length (in bytes) of any single pattern               |
| `full_text`       | The sequence of bytes (values 0–255) to be compressed             |

## Decision Variables

### Pattern Dictionary (`slice`)

Each of the `max_pattern` patterns is represented as a **slice** of the original `full_text`, described by:

- `start` — the position in `full_text` where the pattern begins
- `len` — the length of the pattern in bytes (0 means the pattern is unused)

Patterns are not independently defined strings; they are always substrings of the original text. This keeps the dictionary compact.

### Text Coverage (`cover`)

For every byte position in `full_text`, `cover` records:

- `pat` — which pattern covers this byte
- `index` — the position within that pattern

Together, these variables ensure that the entire text is exactly covered by a sequence of non-overlapping pattern occurrences, laid out left-to-right with no gaps.

### Prefix Code Tree (`parent`, `used_nodes`, `cost`)

Patterns receive variable-length binary codes through a binary **prefix code tree** (like a Huffman tree):

- Each pattern corresponds to a **leaf node** in the tree.
- **Internal nodes** form the branching structure (only `used_nodes` internal nodes are active).
- `parent[n]` — the parent internal node of each non-root tree node.
- `cost[n]` — the **depth** of node `n` in the tree, which equals the **bit length** of its code. The root has cost 0; each level adds 1 bit.
- Every active internal node must have exactly 2 children (it is a proper binary tree).

### Pattern Usage (`uses`)

`uses[p]` counts how many times pattern `p` is referenced in the coverage of the full text (i.e., how many times it "starts" a new occurrence).

## Objective

The model **minimizes** the total encoded size:

$$\text{objective} = \sum_{p \in \text{Pattern}} \Bigl( \texttt{slice}[p].\texttt{len} \times 8 + \texttt{cost}[\text{Leaf}(p)] \times (\texttt{uses}[p] + 1) \Bigr)$$

Each term has two parts:

- $\texttt{slice}[p].\texttt{len} \times 8$ — the cost (in bits) of storing the raw bytes of pattern $p$ in the dictionary (8 bits per byte).
- $\texttt{cost}[\text{Leaf}(p)] \times (\texttt{uses}[p] + 1)$ — the cost of encoding all occurrences of pattern $p$ with its prefix code, plus one extra for the code entry in the table itself.

Unused patterns (with `len = 0`) contribute nothing to the objective.

## Constraints

- Every byte in `full_text` is covered exactly once, in left-to-right order, by the patterns.
- Pattern boundaries align correctly: each new pattern use starts at index 1, and the last byte of the text closes a complete pattern.
- The code tree is a valid full binary tree: every active internal node has exactly 2 children.
- Leaf nodes for unused patterns are excluded from the tree.

## Notes

This model appeared in the **MiniZinc Challenge 2024** with five benchmark instances ranging from short binary sequences to a snippet of Lorem Ipsum text.

The formulation is an original constraint programming model of combined dictionary + prefix-code compression. It is closely related to the concepts underlying classical algorithms such as LZ77/LZ78 and Huffman coding, but frames the joint optimisation as a single CP problem rather than applying the two stages independently.

> **Note for experts:** It is unclear whether this model is directly derived from a specific academic publication. If you are aware of a reference, please update this README accordingly.

## Model update summary

Added concise inline comments in compression.mzn to clarify:

- cover semantics for mapping each text byte to a pattern-position pair,
- tree-depth cost interpretation as codeword length,
- objective decomposition into dictionary and encoded-reference costs.
