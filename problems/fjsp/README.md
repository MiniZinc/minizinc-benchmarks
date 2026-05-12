# Flexible Job Shop Scheduling

This MiniZinc model solves a **Flexible Job Shop Scheduling Problem (FJSP)**. In this problem, each job is made up of a sequence of tasks that must be performed in order. Unlike the standard job shop problem, a task may be processed on **one of several alternative machines**, often with a different processing time depending on the chosen machine. The goal is to build a schedule that respects job order and machine capacity while finishing all jobs as early as possible.

## What the model represents

- **Jobs** are the items that need to be completed.
- **Tasks** are the ordered operations inside each job.
- **Optional tasks** represent the alternative machine choices for a task.
  - For example, one task might be allowed on machine 1 in 4 time units or on machine 3 in 6 time units.
  - The model selects exactly one of these alternatives.
- **Machines** can process at most one selected task at a time.

## Main decision variables

The model uses the following main variables:

- `start[t]`: the start time of task `t`.
- `dur[t]`: the duration of task `t`.
  - This is determined by the machine alternative that is chosen for the task.
- `b[o]`: a Boolean variable that is true when optional task `o` is selected.
  - Since each optional task corresponds to one machine choice, these variables encode the machine assignment.
- `objective`: the makespan, meaning the time by which all jobs are finished.

## Important input data

The key input parameters are:

- `no_mach`, `no_jobs`, `no_task`, `no_optt`: numbers of machines, jobs, tasks, and optional task alternatives.
- `tasks[j]`: the set of tasks belonging to job `j`.
- `optts[t]`: the set of machine alternatives available for task `t`.
- `optt_mach[o]`: the machine used by optional task `o`.
- `optt_dur[o]`: the processing time of optional task `o`.

The model also computes helper arrays such as the job owning each task, minimum and maximum possible durations, and a planning horizon used to bound time variables.

## Constraints in the model

The schedule is built using four main groups of constraints:

1. **Job precedence constraints**  
   Tasks within the same job must follow their required order. A task can start only after the previous task of the same job has finished.

2. **Alternative-selection constraints**  
   For each task, the model chooses exactly one allowed machine alternative. If a task has only one possible machine, that option is forced.

3. **Duration-linking constraints**  
   Once an alternative is chosen, the duration of the task must match the processing time of that chosen alternative.

4. **Machine capacity constraints**  
   A machine cannot process two selected tasks at the same time. This is enforced with a cumulative resource constraint of capacity 1 for each machine.

## Objective

The model **minimizes the makespan**:

- each job’s final task must finish no later than `objective`, and
- the solver searches for the smallest such value.

In practical terms, it tries to finish the full set of jobs as early as possible.

## Model update summary

Added concise inline comments in `fjsp.mzn` to clarify:

- the task timing and duration variables (`start`, `dur`) and their roles in building a schedule,
- the machine selection boolean variables (`b`) that encode alternative machine choices, and
- the objective variable representing the makespan to be minimized.

## Notes and assumptions

This model is clear and compact, but it appears to assume that the tasks of each job are numbered in execution order, since the precedence rule links task `i` to task `i + 1`. If an instance uses a different numbering scheme, that part should be checked by another expert.

## Background and possible references

Flexible job shop scheduling is a well-known extension of the classical job shop scheduling problem. A commonly cited early reference is:

- Brandimarte, P. (1993). _Routing and scheduling in a flexible job shop by tabu search_. Annals of Operations Research, 41, 157–183.

This README is based on the MiniZinc model itself. I could not confirm from the file alone whether the model was taken directly from a specific paper or benchmark source, so that provenance may need to be added by another expert if required.
