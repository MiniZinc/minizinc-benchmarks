# YuMiScheduler: Dual-Arm Robot Task Scheduling

## **Overview**

This MiniZinc model represents a **task scheduling problem for a dual-arm collaborative robot (YuMi)**. The goal is to assign tasks to two robotic arms, determine their execution order, and compute timings while respecting constraints such as travel times, task durations, and collision avoidance. The model aims to minimise the overall makespan (total completion time) for all tasks.

---

## **Problem Description**

The YuMi robot has **two arms** that can perform tasks at different locations. Each task has:

- A **duration** (time to complete).
- A **location** where it must be executed.
- Possible **precedence constraints** (some tasks must be done before others).
- **Travel times** between locations for each arm.

The model must:

- Assign tasks to either the left or right arm.
- Sequence tasks for each arm, including dummy start and end tasks.
- Calculate arrival, start, and end times for each task.
- Ensure arms do not collide and respect physical constraints.
- Minimise the makespan (total time to finish all tasks).

---

## **Key Inputs**

- `no_agents`: Number of arms (typically 2).
- `no_locations`: Number of locations where tasks can be performed.
- `no_actual_tasks`: Number of real tasks (excluding dummy start/end tasks).
- `task_durations[agent, task]`: Duration of each task for each arm.
- `left_arm_travel_times[i,j]`, `right_arm_travel_times[i,j]`: Travel times between locations for each arm.
- Sets defining task categories (e.g., tray tasks, fixture tasks, suction tasks).

---

## **Decision Variables**

- `agent[t]`: Which arm performs task `t`.
- `task[i]`: Position of task `i` in the overall sequence.
- `successor[i]`: The next task after task `i` in the sequence.
- `location[t]`: Location where task `t` is executed.
- `arrival_time[t]`, `start_time[t]`, `end_time[t]`: Timing variables for each task.
- `travel_time[t]`: Time to move from one task to the next.
- `waiting_time[t]`: Time spent waiting before starting a task.
- `makespan`: Total completion time for all tasks (objective).

---

## **Constraints**

1. **Hamiltonian Circuit:**  
   All tasks (including dummy start/end tasks) form a single sequence connecting both arms.
2. **Task Assignment:**  
   Each task is assigned to one arm, and dummy tasks are fixed to their respective arms.
3. **Location Validity:**  
   Tasks must be assigned to valid locations based on their type.
4. **Timing Consistency:**
   - Start time = arrival time + waiting time.
   - End time = start time + duration.
   - Next arrival time = end time + travel time.
5. **Collision Avoidance:**  
   Arms must not interfere with each other during execution.
6. **Precedence Constraints:**  
   Certain tasks must follow others in the sequence (e.g., pick-and-place operations).

---

## **Objective**

Minimise:

```minizinc
makespan = period + cycle_overlap;
```

Where:

- `period` = time until the first arm finishes its tasks.
- `cycle_overlap` = overlap between the two arms' schedules.

---

## **Applications**

- Industrial assembly line optimisation.
- Collaborative robotics scheduling.
- Flexible manufacturing systems.

---

## **References**

- Inspired by collaborative robot scheduling problems in industrial automation.
- Related research: CPAIOR papers on dual-arm robot task planning.

---
