# Stripboard Layout Optimisation

## **Overview**

This MiniZinc model creates an optimal layout for **electrical components on a stripboard**. A stripboard is a prototyping board with parallel copper strips used to build electronic circuits. The goal is to place components and jumper links on the board so that:

- All components fit within the board dimensions.
- Electrical connections between pins are correctly established.
- The overall board area is minimised.

This problem is a **constraint optimisation problem** combining geometric placement and connectivity constraints.

---

## **Problem Description**

- **Inputs:**

  - Board size limits: `max_w` (width), `max_h` (height), and `max_links` (maximum jumper links).
  - Components with:
    - Footprint dimensions (`footprint_w`, `footprint_h`).
    - Allowed orientations (`allowed_orientation`).
    - Pin positions (`pin_dx`, `pin_dy`) and associated nets (`pin_net`).
  - Jumper links with positions and lengths.
  - Nets defining electrical connectivity between pins.

- **Goal:** Arrange components and jumper links on the board without overlaps, ensure correct electrical connections, and minimise the board area.

---

## **Decision Variables**

- **Component Placement:**

  - `component_x`, `component_y`: Position of each component.
  - `component_orientation`: Orientation (Upright, Clockwise, UpsideDown, Anticlockwise).

- **Jumper Links:**

  - `link_x`, `link_y`: Position of each link.
  - `link_length`: Length of each link.

- **Pads and Connections:**

  - `pad_x`, `pad_y`: Coordinates of each pad (pins and link ends).
  - `connection`: Net assignment for each pad.
  - `parent`, `distance`: Used to form a tree structure for connectivity.

- **Board Dimensions:**
  - `board_w`, `board_h`: Computed width and height of the layout.
  - `objective`: Board area (`board_w * board_h`).

---

## **Constraints**

1. **Component Orientation:**  
   Each component must use an allowed orientation.

2. **Non-overlapping Placement:**  
   Components and jumper links cannot overlap and must fit within the board.

3. **Pin Positioning:**  
   Pin pads are placed based on component position and orientation.

4. **Electrical Connectivity:**

   - Pins are assigned to their respective nets.
   - Jumper links connect pads or remain unconnected.
   - Pads in the same net form a directed acyclic graph (DAG) ensuring connectivity.

5. **Physical Connection:**  
   Pads connected in the DAG must be physically adjacent on the stripboard.

6. **Symmetry Breaking:**  
   Reduces equivalent solutions by ordering links and unused positions.

---

## **Objective**

Minimise:

```minizinc
objective = board_w * board_h;
```

This ensures the most compact layout possible.

---

## **Applications**

- PCB and stripboard design automation.
- Optimising space in electronic prototypes.
- Educational tools for circuit design.

---

## **References**

- Stripboard design principles: <https://en.wikipedia.org/wiki/Stripboard>
- Related research: Constraint-based PCB layout optimisation.

---
