# Japanese Character Encoding Detection

## Problem Description

Japanese text can be stored using several different character encodings, the most common being **EUC-JP**, **Shift-JIS (SJIS)**, and **UTF-8**. Each encoding represents Japanese characters using different byte sequences. When text files from different sources are merged — or when the original encoding is unknown — you may end up with a raw byte stream that mixes multiple encodings. Without knowing which bytes belong to which encoding, the text becomes unreadable.

This model tackles the problem of **recovering the original encoding for each byte in a raw byte stream**. Given the stream of bytes as input, it assigns each byte to the encoding most likely responsible for producing it, based on statistical frequency tables and the structural rules of each encoding.

## Encodings Modelled

| Label     | Encoding  | Description                                                             |
| --------- | --------- | ----------------------------------------------------------------------- |
| `ascii`   | ASCII     | Standard 7-bit ASCII characters (bytes 0–127)                           |
| `euc_jp`  | EUC-JP    | 2-byte Japanese encoding, lead bytes A1–FC                              |
| `sjis`    | Shift-JIS | 2-byte Japanese encoding, lead bytes 81–9F / E0–FC or 1-byte kana A1–DF |
| `utf8`    | UTF-8     | Variable-length encoding (2, 3, or 4 bytes for Japanese characters)     |
| `unknown` | Unknown   | Bytes that cannot be classified into any encoding                       |

## Input

| Parameter | Description                                                                           |
| --------- | ------------------------------------------------------------------------------------- |
| `len`     | The number of bytes in the input stream                                               |
| `stream`  | An array of `len` integers (each in the range 0–255) representing the raw byte stream |

## Decision Variables

| Variable      | Domain          | Description                                                                                    |
| ------------- | --------------- | ---------------------------------------------------------------------------------------------- |
| `encoding`    | 0..4 per byte   | The encoding assigned to each byte: ASCII (0), EUC-JP (1), SJIS (2), UTF-8 (3), or Unknown (4) |
| `byte_status` | 0..15 per byte  | The structural role of each byte within its encoding (e.g., first byte, continuation byte)     |
| `char_start`  | 0 or 1 per byte | Whether this byte is the first byte of a new character (`1`) or a continuation byte (`0`)      |
| `n_unknown`   | 0..len          | Total count of bytes assigned the "unknown" encoding                                           |
| `objective`   | 0..maxObj       | The total cost of the assignment (see Objective below)                                         |

### Byte Status Labels

The `byte_status` variable tracks the structural position of each byte within its multi-byte sequence:

- `b_ascii` — a standalone ASCII character
- `b_euc1`, `b_euc2` — first and second byte of an EUC-JP 2-byte character
- `b_sjis1_1` — single-byte Shift-JIS kana character (A1–DF)
- `b_sjis2_1`, `b_sjis2_2` — first and second byte of a 2-byte Shift-JIS character
- `b_utf8_2_1`, `b_utf8_2_2` — first and second byte of a 2-byte UTF-8 sequence
- `b_utf8_3_1`–`b_utf8_3_3` — bytes of a 3-byte UTF-8 sequence
- `b_utf8_4_1`–`b_utf8_4_4` — bytes of a 4-byte UTF-8 sequence
- `b_unknown` — unclassifiable byte

## Constraints

The model enforces:

1. **Encoding–status consistency**: The `encoding` label for each byte must match a valid `byte_status` for that encoding (e.g., a byte labelled EUC-JP must have status `b_euc1` or `b_euc2`).
2. **Byte range validity**: Each byte value must fall within the valid byte ranges defined by its status. For example, a UTF-8 3-byte lead byte must be in the range 224–239, and the two following bytes must be continuation bytes in the range 128–191.
3. **Sequence continuity**: Continuation bytes must immediately follow their lead byte (e.g., `b_euc2` must follow `b_euc1`, `b_utf8_3_2` must follow `b_utf8_3_1`, etc.).
4. **Character start flags**: Lead bytes set `char_start = 1`; continuation bytes set `char_start = 0`.

## Objective

The model **minimises** a cost function that combines two components:

1. **Statistical encoding cost**: For each byte assigned to EUC-JP, SJIS, or UTF-8, the model looks up a precomputed score from a table. These scores approximate $-\log(\text{probability}) \times 10$ — that is, how surprising it would be to see that byte value in that encoding. Minimising this total cost is equivalent to maximising the likelihood that the observed bytes were produced by the assigned encodings.

2. **Unknown penalty**: Each byte classified as "unknown" incurs a large fixed penalty of 1000, strongly discouraging the model from giving up on classifying bytes.

$$\text{objective} = \sum_{i=1}^{len} \text{score}(\text{encoding}_i, \text{stream}_i) + 1000 \times n\_unknown$$

The score tables (`sjis_score`, `eucjp_score`, `utf8_score`) are defined over all 256 possible byte values. Bytes that are impossible or highly improbable under a given encoding have high scores, while common bytes have low scores.

## Notes

- The byte-range rules in this model use a specific variant of EUC-JP known as **CP51932**, which excludes certain lead-byte ranges.
- The UTF-8 constraints cover 2-byte, 3-byte, and 4-byte sequences. Most Japanese characters require 3-byte UTF-8 sequences.
- When bytes are ambiguous (valid under multiple encodings), the model resolves the ambiguity using the statistical score tables.
- The source of the probability/score tables is not documented in the model file. It is likely derived from a corpus of Japanese text, but further verification would be needed to confirm this.

## References

This problem appears to be an original constraint programming formulation of the classical **charset detection** problem for Japanese encodings. Similar heuristic approaches are described in the context of automatic character encoding detection tools such as:

- Mozilla's **chardet** library (originally by Shanjian Li and Rong Gong), which uses frequency tables and state machines for encoding detection.
- The general problem of encoding detection is discussed in: Géry, M., & Haddad, H. (2003). _Evaluation of Web Documents Automatic Language and Encoding Recognition_. Proceedings of the 2003 ACM symposium on Applied computing.
