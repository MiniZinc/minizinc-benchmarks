# MiniZinc Model: Pentominoes Placement with Regular Constraints

## **Overview**

This MiniZinc model addresses the **Pentominoes placement problem**, which involves arranging a set of irregular tiles (pentominoes) on a square board without overlaps and covering the entire board. The approach follows the integer model described in:

_Lagerkvist and Pesant, "Modeling Irregular Shape Placement Problems with Regular Constraints"._

The model uses **regular constraints** to enforce valid tile placements and orientations, making it suitable for solving complex shape-fitting puzzles.

---

## **Problem Description**

- **Goal:** Place all given pentomino tiles on an `n × n` board such that:
  - Each tile occupies a unique set of squares.
  - The entire board is filled without gaps or overlaps.
- **Input:** A set of regular expressions representing valid placements and orientations of tiles.

---

## **Parameters**

- `int: size`  
  The dimension of the square board (e.g., `size = 8` for an 8×8 board).
- `int: tiles`  
  The number of pentomino tiles to place.
- `array[int] of string: expressions`  
  Regular expressions encoding valid sequences of tiles and markers for each row.
- `int: marker = tiles + 1`  
  A special marker used to separate rows in the regular constraint.

---

## **Sets**

- `set of int: Tiles = 1..tiles`  
  Identifiers for each tile.
- `set of int: TilesAndMarker = Tiles union {marker}`  
  Includes both tile identifiers and the marker.

---

## **Decision Variables**

- `array[1..size, 1..size] of var Tiles: board`  
  Represents the board configuration, where each cell contains the ID of the tile occupying it.
- `array[int] of var TilesAndMarker: board_and_markers`  
  A flattened representation of the board with markers inserted to separate rows, used for applying regular constraints.

---

## **Constraints**

- **Regular Constraint:**  
  Ensures that the sequence of tiles and markers matches one of the valid patterns:
  ```minizinc
  constraint forall(expression in expressions)(
      regular(board_and_markers, expression)
  );
  ```

This enforces correct tile placement and orientation across the board.

---

## **Objective**

The model uses:

```minizinc
solve satisfy;
```

The goal is to find **any valid arrangement** of pentominoes that satisfies all constraints.

---

## **Output**

The solution prints the board configuration:

    board =
    <tile IDs arranged in a grid>

---

## **References**

- Lagerkvist & Pesant: _Modeling Irregular Shape Placement Problems with Regular Constraints_.
- <https://github.com/zayenz/minizinc-pentominoes-generator>.

---
