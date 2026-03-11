# Portal (MiniZinc model) — Beginner-friendly overview

This model encodes a **grid puzzle inspired by Portal-like mechanics**. A player starts at one position and heading, can move or rotate, can shoot portals onto walls, and must reach a goal cell in as few time steps as possible.

## 1) Problem being modeled

The input is a rectangular board (`inputBoard`) made of characters such as:

- `X` = wall (portal can be placed on it)
- `N` = wall where portals are **not** allowed
- `O` = pit (player cannot stand on it)
- space = empty
- `!` = goal (exactly one)
- `^`, `v`, `<`, `>` = player start + initial heading (exactly one)

A horizon `maxTime` is given. The model creates a plan of actions over time so that the player reaches the goal.

## 2) Main decision variables

For each time step `t = 1..maxTime`:

- `playerPos[t]`: player grid position `(x,y)`
- `playerHeading[t]`: one of `{North, South, East, West}`
- `playerAction[t]`: one of `{Move, Left, Right, Shoot}`
- `portal1Pos[t]`, `portal2Pos[t]`: optional positions of up to two portals

So the solver decides **what action to take at each step**, and this determines all future states.

## 3) Key constraints (game rules)

- Start state is fixed from the board; final position at `maxTime` must be the goal.
- Player cannot be in a pit.
- If portal 1 exists, it must be different from portal 2.
- Heading update follows action (`Left`/`Right` rotate, `Move`/`Shoot` keep heading).
- `Move` advances one cell in the current heading.
  - If entering portal 1, player is teleported to portal 2.
  - If entering portal 2, player is teleported to portal 1.
  - Otherwise movement is allowed only onto `Empty` cells.
- `Shoot` can place a portal at the first hittable wall in the current direction.
  - New portal becomes `portal1`; old `portal1` shifts to `portal2`.
  - `WallNoPortal` blocks shooting but cannot host a portal.

The model precomputes `nextWall[y,x,heading]` to quickly know where a shot would land.

## 4) Objective

The model computes:

- `foundGoalAtStep`: first time index where `playerPos[t] == goalPos`

and **minimizes** `foundGoalAtStep`.

So it is an optimization model for the **earliest goal reach time** (within `maxTime`).

## 5) Notes on symmetry-breaking constraints

Extra constraints remove obviously redundant action patterns (for example immediate opposite turns). This does not change intended solutions, but helps prune equivalent action sequences.

## 6) Uncertainties / assumptions (from reading the model)

- Portal shooting appears to target only cells of type `Wall`, not `WallNoPortal`; this is explicit in `nextWall`.
- Entering the goal cell seems possible only when it is reached as the final required position; intermediate movement rule allows stepping only onto `Empty` (not directly onto `goal`) unless teleport behavior leads there. This is inferred from transitions and may be an intentional modeling choice.
- The model file itself does not cite an external benchmark/source publication.

## References

- MiniZinc model source: `portal.mzn` (same folder)
- Game concept inspiration: Valve’s _Portal_ series (high-level thematic inspiration; no formal citation in the model)
