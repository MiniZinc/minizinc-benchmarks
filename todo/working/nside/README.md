# N-SITE: Road Network Maintenance Scheduling

## Problem Description

The **N-SITE problem** is a road network maintenance scheduling problem. The goal is to decide _which_ maintenance worksheets to carry out, and _when_ to schedule them, across a fixed planning horizon of several days.

Each **worksheet** represents a maintenance job that occupies one or more roads for a contiguous sequence of days. A worksheet is assigned to a **work center** that supplies the workers needed to carry it out. Every worksheet has an associated **importance** value reflecting how valuable it is to complete.

The challenge is to select and schedule worksheets so that:

- important work gets done,
- the road network is not excessively disrupted, and
- all resource and scheduling constraints are respected.

## Parameters

| Parameter                    | Description                                                                                                                         |
| ---------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `days`                       | Number of days in the planning horizon                                                                                              |
| `roads`                      | Number of roads in the network                                                                                                      |
| `centers`                    | Number of work centers                                                                                                              |
| `worksheets`                 | Number of worksheets to consider                                                                                                    |
| `activities`                 | Maximum number of daily activities within any worksheet                                                                             |
| `perterb`                    | Perturbation cost of using a road on a given day (note: "perterb" appears to be a spelling of "perturb" used in the original model) |
| `available_workers[c]`       | Number of workers available at work center `c` each day                                                                             |
| `w_id[w]`                    | External identifier for worksheet `w`                                                                                               |
| `work_center[w]`             | The work center responsible for worksheet `w`                                                                                       |
| `mandatory[w]`               | Whether worksheet `w` must be executed (1 = mandatory, 0 = optional)                                                                |
| `importance[w]`              | Importance score of worksheet `w`                                                                                                   |
| `est[w]`                     | Earliest day worksheet `w` may start                                                                                                |
| `lst[w]`                     | Latest day worksheet `w` may start                                                                                                  |
| `duration[w]`                | Number of days worksheet `w` takes to complete                                                                                      |
| `road[w, a]`                 | The road used by worksheet `w` on its `a`-th day of activity (-1 = no road used)                                                    |
| `workers[w, a]`              | Number of workers worksheet `w` requires on its `a`-th day                                                                          |
| `blocked_max_amount[b]`      | Maximum number of roads from set `b` that may be blocked simultaneously                                                             |
| `blocked_roads[b]`           | The set of roads covered by blocking rule `b`                                                                                       |
| `preceeds[i]`, `succeeds[i]` | Worksheets involved in precedence rule `i`: `preceeds[i]` must finish before `succeeds[i]` starts (when both are executed)          |

## Decision Variables

| Variable | Description                                                    |
| -------- | -------------------------------------------------------------- |
| `g[w]`   | 1 if worksheet `w` is executed, 0 otherwise                    |
| `d[w]`   | The start day of worksheet `w`                                 |
| `e[w]`   | The end day of worksheet `w` (derived as `d[w] + duration[w]`) |

## Constraints

1. **Time windows**: Every worksheet must start no earlier than its earliest start time and no later than its latest start time.
2. **Schedule fit**: Every worksheet must finish within the planning horizon.
3. **Mandatory worksheets**: Worksheets marked as mandatory must be executed.
4. **Precedence**: If two worksheets are both executed and a precedence rule exists between them, the first must finish before the second begins.
5. **Road blocking limits**: For each defined group of roads, the number of roads in that group being worked on simultaneously on any given day must not exceed a specified maximum. This prevents too much of the network being disrupted at once.
6. **Work center capacity**: On every day, for each work center, the total number of workers in use across all worksheets from that center must not exceed the center's available workforce.

## Objective

The model maximises:

$$\text{objective} = \text{importance\_obj} - \text{perterb\_obj}$$

where:

- **`importance_obj`** is the sum of importance values of all executed worksheets.
- **`perterb_obj`** is the _maximum_ total perturbation cost across all days, measuring how much the road network is disrupted on the worst day.

The objective therefore rewards completing high-importance worksheets while penalising large disruptions to the road network.

## Notes

- The variable `g[w] = 0` (not executed) is coupled to `d[w] = est[w]` as a modelling convention to fix unused start times to a canonical value.
- The problem originates from real-world road maintenance scheduling (the name "N-SITE" suggests an industry or government project context). An exact academic reference has not been confirmed; if you are aware of a publication describing this problem, please add a citation here.
