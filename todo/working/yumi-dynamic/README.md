# yumi-dynamic (MiniZinc model) — beginner-friendly guide

## What problem is this model solving?

This model schedules tasks for a **dual-arm ABB YuMi-style robot cell**.  
You can think of it as: *two robot arms must perform a set of assembly-related tasks, move between locations, avoid collisions, and repeat this work in a cycle as fast as possible*.

The model combines:
- **Task assignment**: which arm does each task.
- **Task ordering/routing**: in what sequence tasks are done.
- **Timing**: when each task starts/ends, including waiting and travel.
- **Collision/resource safety**: both arms must not occupy conflicting zones at the same time.

It uses a cyclic schedule idea: each arm has dummy start/end tasks, and the route is represented as one circuit that links both arm sequences.

---

## Main inputs (from data)

The `.mzn` file expects several data structures (provided in the JSON instances in `data/`), including:
- Task durations per arm.
- Travel-time matrices for left and right arm.
- Task categories (tray/camera/fixture/output) and allowed locations per category.
- Ordered task chains (fixture orders, suction pick-place orders, gripper pick-place orders).
- Zone occupancy definitions for work/wait/travel for each arm and location pair.
- Capacity-related data (e.g., number of suction cups, empty-gripper-required tasks).

So, the model is not just routing; it is a **routing + scheduling + collision-avoidance** model driven by detailed workspace geometry data.

---

## Decision variables (high level)

Key variable groups are:
- `agent[t]`: which arm executes task `t`.
- `successor[t]` and `task[pos]`: two equivalent encodings of task sequence/circuit.
- `location[t]` and `next_location[t]`: chosen location for each task and the next task’s location.
- Time variables per task: `arrival_time`, `start_time`, `end_time`, `waiting_time`, `travel_time`, `next_arrival_time`.
- Objective-related totals: `period`, `makespan`, `cycle_overlap`.
- Zone-blocking binaries per task and zone: `task_blocker`, `wait_blocker`, `travel_blocker`.

---

## What constraints does it enforce?

In plain terms, the model enforces:
- **Valid cyclic routes** using `circuit(successor)` plus depot/dummy-task structure.
- **Agent consistency**: each task and its successor must stay on the same arm sequence (except arm-boundary depot links).
- **Location validity**: each task must use a location from its allowed set.
- **Travel-time consistency**: travel time depends on arm + current location + next location (via table constraints).
- **Time flow consistency**: arrival → start → end → travel → next arrival.
- **Task order rules** for fixture/suction/gripper chains.
- **Tool capacity rules** (gripper load, suction load).
- **Collision/safety rules** using zone occupancy and cumulative/diffn formulations.
- **Layout realism** such as all tray tasks at different tray locations.

Some constraints are marked as implied/redundant and controlled by flags (`implied_*`, `using_*`) to tune propagation.

---

## Objective

The model solves:

- `solve ... minimize period;`

where:
- `period` is defined as the minimum of the two arm end times (in the cyclic interpretation).
- `makespan = period + cycle_overlap` is also tracked, but **not** directly minimized.

So the optimization target is the cycle period, with additional constraints tying period/makespan/timing together.

---

## Notes for beginners

- This is a **rich CP model** (global constraints + many table constraints), so solving can be sensitive to data size.
- The model includes a search annotation (`seq_search(...)`), but this README focuses on the model meaning rather than solver search strategy.
- If you are new to MiniZinc, start by inspecting one small instance in `data/` and printing a few core outputs (`agent`, `task`, `arrival_time`, `location`).

---

## Uncertainty / interpretation caveats

- The exact physical meaning of every task ID depends on instance data and external process context.
- The model comments mention a paper reference placeholder (`[To be inserted]`), so a formal publication link is not directly available inside this file.
- The exact semantics of `period` in the real production system may depend on conventions outside this repository, even though the mathematical definition is explicit in the model.

---

## Identifiable references

- Model header credits **Johan Ludde Wessén** (`YuMiScheduler`, latest update noted as 2021-06-23).
- License header in the model states **MIT License**.
- Benchmark metadata shows usage in MiniZinc challenge sets (including 2021 and 2024 instance lists in `metadata.json`).
