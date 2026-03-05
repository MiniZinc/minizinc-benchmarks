# Text Compression Model

## Overview

This MiniZinc model represents a **text compression problem**. The goal is to compress a given sequence of bytes (`full_text`) by identifying repeated patterns and encoding them efficiently using prefix codes. The objective is to minimise the total size of the compressed representation.

---

## Problem Description

We are given:

- A sequence of bytes (`full_text`) representing the original text.
- A maximum number of patterns (`max_pattern`) and maximum pattern length (`max_pattern_len`).

The model:

1. Splits the text into **patterns** (substrings).
2. Assigns each pattern a **prefix code** using a binary tree structure.
3. Ensures the entire text is covered by these patterns in sequence.
4. Calculates the cost of storing patterns and their codes.
5. Minimises the total encoding size.

---

## Key Components

### Input

- `full_text`: Array of bytes (0–255) representing the original text.
- `max_pattern`: Maximum number of distinct patterns allowed.
- `max_pattern_len`: Maximum length of any pattern.

### Decision Variables

- `slice[p]`: For each pattern `p`, stores:
  - `start`: Starting index in `full_text`.
  - `len`: Length of the pattern.
- `cover[i]`: For each position `i` in `full_text`, indicates:
  - `pat`: Which pattern covers this position.
  - `index`: Position within the pattern.
- `parent[n]`: Parent node in the prefix code tree for node `n`.
- `cost[n]`: Depth of node `n` in the prefix tree.
- `uses[p]`: Number of times pattern `p` is used in the text.

---

## Constraints

1. **Text Coverage**:
   - Every byte in `full_text` is covered by a pattern.
   - Patterns cover consecutive positions correctly.
2. **Prefix Code Tree**:
   - Internal nodes have exactly two children.
   - Leaf nodes correspond to patterns that are actually used.
   - Cost of a node equals its parent's cost plus one.
3. **Pattern Usage**:
   - Patterns with zero length are considered unused.

---

## Objective

Minimise:

$$
\text{objective} = \sum_{p \in \text{Pattern}} \big( \text{slice}[p].\text{len} \times 8 + \text{cost}[\text{Leaf}(p)] \times (\text{uses}[p] + 1) \big)
$$

This combines:

- **Pattern storage cost**: Length × 8 bits.
- **Encoding cost**: Depth of the pattern's code × number of uses.

---

## Notes

- The model uses **global_cardinality** to enforce tree structure constraints.
- The prefix code tree ensures efficient encoding similar to Huffman coding.
- This approach is suitable for optimising dictionary-based compression schemes.

---

### References

- Huffman, D. A. (1952). _A Method for the Construction of Minimum-Redundancy Codes_.
