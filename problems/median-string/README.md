# Median String

## Problem Description

Given a set of strings over a finite alphabet, the **Median String Problem** asks for a string (the _median_) that minimises the total edit distance to all strings in the set. Informally, the median string is the "most central" or "most representative" string of the collection.

This problem has important applications in:

- **Bioinformatics** — finding a consensus sequence from a set of DNA, RNA, or protein sequences.
- **Pattern recognition** — identifying a prototype or exemplar from a set of observed strings.
- **Data mining and clustering** — computing a centroid for string-based clusters.

The edit distance used in this model is the **insertion/deletion (indel) distance**: the minimum number of single-character insertions and deletions required to transform one string into another. Unlike standard Levenshtein distance, substitutions are not allowed as a single atomic operation; a substitution must be performed as a deletion followed by an insertion.

Strings of varying length are represented within fixed-size arrays by padding shorter strings with a special null character (encoded as `0`). The model handles these padding characters correctly when computing distances.

## Parameters

| Parameter            | Description                                                                                                                                                                  |
| -------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `num_strings`        | The number of input strings in the set                                                                                                                                       |
| `max_length_strings` | The (fixed) array length used to store each input string (including any padding)                                                                                             |
| `max_char`           | The size of the alphabet; characters are encoded as integers `1..max_char`, with `0` representing a padding/null character                                                   |
| `max_length_median`  | The maximum permitted length of the median string                                                                                                                            |
| `strings`            | A 2D array of integers encoding the input strings; `strings[i, j]` is the `j`-th character of the `i`-th string, with `0` used for padding beyond the string's actual length |
| `str_length`         | The actual (unpadded) length of each input string                                                                                                                            |

## Variables

| Variable       | Description                                                                                                                                                                                                                                               |
| -------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `median`       | An array of decision variables representing the characters of the median string. Each element takes a value in `0..max_char`, where `0` means the position is unused (padding). The model ensures positions beyond `max_length_median` are forced to `0`. |
| `distances[i]` | The edit distance between the `i`-th input string and the median string candidate                                                                                                                                                                         |
| `objective`    | The total sum of edit distances from the median string to all input strings                                                                                                                                                                               |

## Objective

The model **minimises** `objective`, i.e. the sum of edit distances from the median string to every input string:

$$\text{minimise} \sum_{i=1}^{\text{num\_strings}} \text{distances}[i]$$

## Key Constraint: Edit Distance via Dynamic Programming

The `lcs_global` predicate encodes a standard dynamic-programming recurrence for computing the indel edit distance between two strings. A triangular table `T[i,j]` is used where `T[i,j]` represents the minimum edit distance between the first `i` characters of one string and the first `j` characters of the other. The boundary conditions initialise the first row and column to their respective indices, and the recurrence propagates as follows:

- If characters match (`S1[i] = S2[j]`): no cost is incurred (`T[i,j] = T[i-1,j-1]`).
- If the first string has a padding character at position `i` (`S1[i] = 0`): the position is skipped (`T[i,j] = T[i-1,j]`).
- If the second string has a padding character at position `j` (`S2[j] = 0`): the position is skipped (`T[i,j] = T[i,j-1]`).
- Otherwise: the best of an insertion or deletion is taken (`T[i,j] = min(T[i-1,j]+1, T[i,j-1]+1)`).

> **Note:** The predicate is named `lcs_global`, which may suggest a relationship to Longest Common Subsequence (LCS). The indel edit distance between two strings is indeed equal to `|S1| + |S2| − 2 × LCS(S1, S2)`, so the two formulations are mathematically equivalent. A reviewer familiar with the original source of this model may be able to clarify the naming choice.

## References

The Median String Problem has been studied extensively in the literature. Relevant works include:

- de la Higuera, C., & Casacuberta, F. (2000). _Topology of strings: Median string is NP-complete_. Theoretical Computer Science, 230(1–2), 39–48.
- Kohonen, T. (1985). _Median strings_. Pattern Recognition Letters, 3(5), 309–313.
- Sim, J. S., & Park, K. (2003). _The consensus string problem for a metric is NP-complete_. Journal of Discrete Algorithms, 1(1), 111–120.

> **Note for reviewers:** If this model originates from a specific paper or benchmark suite, please add the corresponding citation here.
