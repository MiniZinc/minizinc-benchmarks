# Waste Water Treatment Plant Scheduling (`wwtpp.mzn`)

## What problem is this model solving?
This MiniZinc model describes a **waste-water treatment plant scheduling** problem over a fixed number of time steps.

Several industries produce wastewater over time. At each time step, wastewater can either:
- be sent directly to the treatment plant, or
- be temporarily stored in an industry buffer tank and released later.

The goal is to find a schedule that respects:
- plant capacity at every time step,
- each tank’s storage and outflow limits,
- flow-conservation over time,
- and many pre-specified on/off operating windows for direct discharge.

This is modeled as a **constraint satisfaction** problem (find any feasible plan), not as an optimization problem.

## Main data (inputs)
The model takes these key parameters:
- `INDUSTRIES`: number of industries.
- `TIMESTEPS`: number of time periods.
- `max_capacitat`: maximum total plant intake per time step.
- `TankFlow[i]`: maximum outflow rate from industry `i`’s tank.
- `TankCapacity[i]`: maximum storage for industry `i`’s tank.

## Decision variables (what the solver chooses)
For each industry `i` and time `j`:
- `c[i,j]`: direct flow from industry `i` to the plant at time `j`.
- `buf[i,j]`: amount stored in industry `i`’s tank at end of time `j`.
- `bout[i,j]`: flow released from tank `i` toward the plant at time `j`.
- `d[i,j]`: wastewater produced (declared as `var int` in this model).

## Core constraints (intuitive view)
1. **Plant capacity:**
   \[
   \sum_i (c[i,j] + bout[i,j]) \le max\_capacitat \quad \forall j
   \]
2. **Tank balance over time:** storage evolves as
   `previous storage - released + produced - direct sent`.
3. **Tank limits:** storage is nonnegative and within `TankCapacity`; release is nonnegative and within `TankFlow`.
4. **Release logic:** at each step, release is either:
   - `0`, or
   - full tank-flow rate (if enough stock), or
   - all remaining stock (if stock is small).
5. **Boundary conditions:** tanks start with no release at step 1 and are forced empty at step 26 (`buf[i,26] = 0`).
6. **Operating windows for direct flow `c`:** a large set of constraints enforces whether each industry can send direct flow in specific time blocks (either all requested flow in block, or none), plus many fixed zeros at specific times.

## Objective
There is **no optimization objective**. The model uses:
- `solve satisfy;`

So the solver returns any schedule that satisfies all constraints.

## Output/search notes
- The model includes a search annotation (`int_search`) over `buf` and `bout`.
- This README intentionally focuses on the mathematical model and does not explain search strategy details.

## Uncertainty and assumptions
Because this single file has limited comments and no explicit narrative for all symbols, a few semantics are inferred:
- `d[i,j]` likely represents generated wastewater demand/production; it is unusual that it is a decision variable rather than fixed input, so additional data/model context may specialize this.
- The long block constraints for `c[i,j]` look like predefined admissible discharge windows (possibly from random instance generation), but exact business interpretation is not fully documented in-file.

## References
Identifiable in-file reference:
- Author comment in model header: **Miquel Bofill** (`mbofill@ima.udg.edu`).

If you want, I can also add a short “How to run” section (MiniZinc CLI/example command) once you confirm the intended `.dzn` instance file(s).