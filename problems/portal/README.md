# MiniZinc Model: Portal Game

## **Overview**

This MiniZinc model represents a simplified version of the **Portal game** played on a 2D grid. The player starts at a given position and must reach a goal position by moving and using portals. The player can move in four directions (up, down, left, right) and shoot portals to teleport across the board. The challenge is to find the shortest sequence of actions to reach the goal.

---

## **Problem Description**

- The board is a rectangular grid containing:

  - **Walls (`X`)**: Blocks movement and portal placement.
  - **Walls without portal (`N`)**: Blocks movement and portals cannot be placed here.
  - **Empty spaces (` `)**: Free cells for movement.
  - **Pits (`O`)**: Dangerous cells; the player cannot step on them.
  - **Goal (`!`)**: The target position to reach.
  - **Player (`^`, `v`, `<`, `>`)**: Indicates initial position and heading (North, South, East, West).

- **Player Actions:**

  - `Move`: Move one square forward.
  - `Left` / `Right`: Rotate 90° left or right.
  - `Shoot`: Fire a portal in the current heading direction.

- **Portal Rules:**

  - A portal travels in a straight line until it hits a wall.
  - Two portals can exist at a time; stepping on one teleports the player to the other.
  - Shooting a third portal removes the oldest one.

- **Objective:** Minimise the number of steps required to reach the goal.

---

## **Inputs**

- `array[int] of string: inputBoard`  
  The board layout as an array of strings.
- `int: maxTime`  
  Maximum number of steps allowed.

---

## **Key Variables**

- `array[Time] of var Pos: playerPos`  
  Player position at each time step.
- `array[Time] of var Heading: playerHeading`  
  Player heading at each time step.
- `array[Time] of var Action: playerAction`  
  Action taken at each time step.
- `array[Time] of var optPos: portal1Pos, portal2Pos`  
  Positions of the two portals over time.
- `Pos: playerInitialPos`  
  Starting position of the player.
- `Heading: playerInitialHeading`  
  Initial heading of the player.
- `Pos: goalPos`  
  Position of the goal.

---

## **Constraints**

1. **Board Validity:**  
   The input board must be rectangular and contain exactly one player and one goal.

2. **Movement Rules:**

   - The player moves one square at a time.
   - Cannot move into walls or pits.
   - Teleportation occurs when stepping onto a portal.

3. **Portal Rules:**

   - Portals cannot overlap.
   - Shooting creates a new portal at the next wall in the current heading.

4. **Action Sequence Rules:**
   - No immediate turn back (e.g., Left then Right).
   - No three consecutive turns in the same direction.
   - Last action before reaching the goal must be `Move`.

---

## **Objective**

Minimise:

```minizinc
foundGoalAtStep
```

This represents the earliest time step at which the player reaches the goal.

---

## **Output**

- A step-by-step trace showing:
  - Time step
  - Player position and heading
  - Action taken
  - Portal positions
- Visual representation of the board at each step.

---

## **References**

- Inspired by the mechanics of the **Portal** video game.
- Demonstrates constraint modelling for pathfinding and dynamic state changes.

---
