# Stripboard Layout

## Problem Description

A **stripboard** (also called Veroboard) is a prototyping circuit board made up of a grid of holes connected by copper strips running in one direction (rows). Components are inserted into the holes and their legs (pins) are soldered to the strips. Pins that land on the same strip are automatically electrically connected. To isolate different parts of a circuit, you can cut a strip between two holes. To connect strips that would otherwise be isolated, you can insert short **jumper wires** (links) that bridge across rows.

Given a set of electronic components, their **footprints** (width and height), their **pin locations** (offsets within the footprint), and a **netlist** (which pins must be electrically connected), the goal is to place all components on the smallest possible board so that:

- every component fits within the board boundary without overlapping any other component or jumper wire,
- all pins belonging to the same net end up electrically connected (via shared strips or jumper wires), and
- pins belonging to different nets are never accidentally connected (gaps are left for strip cuts).

## Decision Variables

| Variable                           | Meaning                                                                                            |
| ---------------------------------- | -------------------------------------------------------------------------------------------------- |
| `component_x`, `component_y`       | Grid position (top-left corner) of each component on the board                                     |
| `component_orientation`            | Rotation of each component: `Upright`, `Clockwise`, `UpsideDown`, or `Anticlockwise`               |
| `link_x`, `link_y`, `link_length`  | Column, starting row, and span of each jumper wire; a link with `link_y = -1` is considered unused |
| `pad_x`, `pad_y`                   | Computed absolute grid position of each electrical pad (component pin or jumper endpoint)          |
| `parent`, `distance`, `connection` | Tree-based bookkeeping variables that track how pads are connected into nets (one DAG per net)     |
| `board_w`, `board_h`               | Width and height of the bounding rectangle actually used by the layout                             |

## Objective

Minimise board area:

$$\text{objective} = \text{board\_w} \times \text{board\_h}$$

## Key Constraints

1. **No overlap** – Component footprints and jumper wires occupy disjoint rectangles on the board (`diffn`).
2. **Pin placement** – Each pin's absolute position is derived from its component's position and orientation.
3. **Connectivity (same net)** – Pads belonging to the same net must be physically adjacent along a strip, forming a connected tree (DAG). Connectivity is maintained through shared row positions and a `disjunctive` scheduling constraint.
4. **Isolation (different nets)** – Pads belonging to different nets must never be adjacent on the same strip (leaving room for a cut between them).
5. **Jumper link nets** – The two endpoints of a jumper wire must belong to the same net; unused links are parked off-board.

## Notes and Uncertainty

- The model supports a configurable maximum number of links (`max_links`). If more links are needed than the instance provides, the problem becomes infeasible, so instances must be chosen (or verified) with a generous enough bound.
- Component orientations are constrained per-component via `allowed_orientation`, meaning some components may be fixed in one direction while others are free to rotate.
- The board size is not fixed in advance; `board_w` and `board_h` are themselves variables bounded by the input parameters `max_w` and `max_h`. The tight bound on board dimensions may affect scalability on large instances.
- The connectivity model uses a DAG/tree structure over pads rather than an explicit routing model, which is an unconventional but compact encoding. The exact behaviour on edge cases (e.g., nets with a single pin) may be worth verifying against the data files.

## References

- **Author:** Jason Nguyen, Monash University (2022)
- **Licence:** MIT
- Stripboard (Veroboard) background: [Wikipedia – Stripboard](https://en.wikipedia.org/wiki/Stripboard)
