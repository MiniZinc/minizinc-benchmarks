# Fox–Geese–Corn

## Overview

This MiniZinc model describes a generalized river-crossing problem based on the classic fox, goose, and corn puzzle. Instead of moving just one fox, one goose, and one bag of corn, the model allows many items of each type and asks:

- how many foxes, geese, and corn units should be moved on each boat trip,
- how many trips should actually be used,
- and which transport plan gives the highest final value on the destination bank.

The setting has two river banks, which the model tracks as **west** and **east**. Initially, all items start on the west bank. Odd-numbered trips move items from west to east, and even-numbered trips move items back from east to west. This means the model can use return trips when that helps preserve or improve the final outcome.

## What the model is solving

The model is not simply trying to move everything across. Instead, it is solving an **optimization** problem: it chooses a transport plan that maximizes the total value of the items that remain safely on the east bank at the end.

This matters because leaving foxes, geese, and corn together without supervision can cause losses. Those interactions are encoded in the predicate `alone(...)`, which updates what remains on a bank after it is left unattended. At a high level, this predicate represents the model's built-in “what gets eaten or lost when left together” rules.

## Parameters

The main input data are:

- `f`, `g`, `c`: the initial numbers of foxes, geese, and corn units.
- `k`: the boat capacity, measured as the maximum total number of items moved on one trip.
- `t`: an upper bound on the number of trips the model may consider.
- `pf`, `pg`, `pc`: the value (or profit) of one fox, one goose, and one corn unit that successfully ends on the east bank.

From these, the model also computes `maxp`, a safe upper bound for the objective value.

## Decision variables

The model makes the following choices:

- `fox[i]`, `geese[i]`, `corn[i]`: how many items of each type are transported on trip `i`.
- `trips`: the number of trips that are actually used, between `0` and `t`.
- `wfox[i]`, `wgeese[i]`, `wcorn[i]`: how many foxes, geese, and corn units are on the west bank after trip `i`.
- `efox[i]`, `egeese[i]`, `ecorn[i]`: how many foxes, geese, and corn units are on the east bank after trip `i`.
- `objective`: the final weighted value of the items on the east bank.

## Main constraints

The model enforces several simple but important rules:

1. **Initial state**  
   At trip `0`, all items are on the west bank and none are on the east bank.

2. **Trip direction**  
   Odd trips send items from west to east. Even trips send items from east back to west.

3. **Bank updates**  
   After each trip, the west-bank and east-bank inventories are updated to reflect what was transported.

4. **Unattended-bank losses**  
   The predicate `alone(...)` determines what survives on the bank that has been left without supervision. This is the key rule that captures the fox/geese/corn interactions.

5. **Boat capacity**  
   For every trip, the total number of transported items must satisfy
   $fox[i] + geese[i] + corn[i] \le k$.

6. **Unused trips carry nothing**  
   If `i > trips`, then trip `i` transports zero foxes, zero geese, and zero corn.

## Objective

The model maximizes

$$
objective = efox[trips] \cdot pf + egeese[trips] \cdot pg + ecorn[trips] \cdot pc
$$

So the best solution is the one that leaves the most valuable combination of surviving items on the east bank after the final used trip.

## Notes on interpretation

- This is best understood as a **generalized optimization version** of the classic river-crossing puzzle, not just the usual yes/no feasibility puzzle.
- The exact loss behavior is defined directly by the `alone(...)` predicate. Some of those rules are more detailed than the usual textbook statement of the puzzle, so anyone reusing the model should read that predicate carefully.
- I could not confirm a specific academic paper from the model file alone. It appears to be derived from the well-known fox–goose–corn family of river-crossing puzzles, but a domain expert may be able to identify a more precise source.

## Related background

This model is closely related to the classic river-crossing puzzle often called **fox, goose, and corn** (or similar variants such as **fox, goose, and beans**), where unsafe combinations cannot be left alone on one bank. The present MiniZinc model extends that idea by allowing larger quantities, return trips, and an explicit value-maximization objective.

## Model update summary

Added concise inline comments in foxgeesecorn.mzn to clarify:

- trip-load decision variable roles,
- objective interpretation on east-bank value,
- optimization direction (maximize recovered value).
