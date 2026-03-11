# Crossword Puzzle (Optimisation)

## Problem Description

This model fills in a crossword puzzle grid with words chosen from a dictionary, aiming to maximise the total **score** of all letters placed on the grid.

A crossword grid is made up of "white" cells (which must contain a letter) and "black" cells (which act as dividers and are left blank). The white cells form a set of word slots — horizontal (across) and vertical (down) — called **clues**. Each clue must be filled with a valid word of the correct length taken from the provided dictionary.

The twist compared to a standard crossword is that the grid template is already fixed (i.e., you know which cells are white or black and where each word slot starts and ends), but the specific words to place are _chosen_ by the solver. The goal is to select words such that the letters placed on the grid achieve the highest possible total score — similar in spirit to a game of Scrabble.

## Letter Values

Each letter of the alphabet carries a point value, inspired by Scrabble tile scores:

| Letter | a   | b   | c   | d   | e   | f   | g   | h   | i   | j   | k   | l   | m   | n   | o   | p   | q   | r   | s   | t   | u   | v   | w   | x   | y   | z   |
| ------ | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Value  | 1   | 3   | 3   | 2   | 1   | 4   | 2   | 4   | 1   | 8   | 5   | 1   | 3   | 1   | 1   | 3   | 10  | 1   | 1   | 1   | 1   | 4   | 4   | 8   | 4   | 10  |

The total score is the sum of the values of every letter placed in a white cell on the grid.

## Input Parameters

| Parameter                                  | Description                                                                                                                      |
| ------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------- |
| `width`, `height`                          | Dimensions of the crossword grid                                                                                                 |
| `grid`                                     | A 2D boolean array indicating which cells are white (`true`) and which are black (`false`)                                       |
| `number_of_clues`                          | The total number of word slots (across and down)                                                                                 |
| `startrow[c]`, `startcol[c]`               | Starting row and column of clue `c`                                                                                              |
| `down[c]`                                  | Whether clue `c` is vertical (`true`) or horizontal (`false`)                                                                    |
| `leng[c]`                                  | The length (number of letters) required for clue `c`                                                                             |
| `words1` .. `words45`, `dict1` .. `dict45` | Dictionary entries grouped by word length; `wordsN` is the count of words of length `N`, and `dictN` is the array of those words |

Words of lengths 1 through 45 are supported.

## Decision Variables

| Variable    | Description                                                    |
| ----------- | -------------------------------------------------------------- |
| `xx[r, c]`  | The letter assigned to each white cell at row `r`, column `c`  |
| `ww[clue]`  | The index of the word chosen from the dictionary for each clue |
| `objective` | The total score — sum of letter values across all white cells  |

## Constraints

1. **Word validity**: Each clue's letter sequence (read horizontally or vertically from its start position) must exactly match a word in the dictionary of the correct length.
2. **No repeated words**: Within any group of clues of the same length, each chosen word must be distinct — i.e., the same word cannot fill two clues of the same length.
3. **Black-cell padding**: Black cells are fixed to the letter `a` internally (this is a modelling convenience; those cells do not contribute meaningfully to the puzzle output).

## Objective

**Maximise** the total score:

$$\text{objective} = \sum_{r, c} \text{value}[\,xx[r,c]\,]$$

The solver seeks an assignment of valid words to all clues such that this sum is as large as possible — favouring words that contain high-value letters like `q`, `z`, `x`, and `j`.

## Notes

- This is the **optimisation** variant of the crossword problem. A simpler satisfaction version would merely require that all clues be filled with valid words.
- The model supports word lengths from 1 to 45 characters, making it applicable to a wide range of grid sizes.
- The crossword benchmark problem appears in the MiniZinc challenge benchmark suite and is related to the classic constraint programming crossword problem studied in, e.g.:
  - Ginsberg, M. L., Frank, M., Halpin, M. P., & Torrance, M. C. (1990). _Search lessons learned from crossword puzzles_. AAAI-90. ([link](https://aaai.org/papers/0210-aaai90-034-search-lessons-learned-from-crossword-puzzles/))
  - Beacham, A., Chen, X., Sillito, J., & van Beek, P. (2001). _Constraint programming lessons learned from crosswords_. IJCAI-01 Workshop on Modelling and Solving Problems with Constraints.

> **Note for reviewers**: The origin and authorship of this specific MiniZinc model (and its associated data files) are not entirely clear. If you know the original source, please update this README accordingly.
