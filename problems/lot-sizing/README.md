# Discrete Lot Sizing

## Problem Description

The **Discrete Lot Sizing** problem is a classic production scheduling problem from manufacturing. A single machine must produce a set of orders, where each order requires producing one unit of a specific item type. The machine can only produce one order per time period, and some periods may be left idle.

Two types of costs must be balanced:

- **Changeover (setup) cost**: whenever the machine switches from producing one item type to a different item type, a setup cost is incurred. This cost depends on which two item types are involved in the switch.
- **Inventory cost**: if an order is completed _before_ its due date, the finished item must be stored until it is needed. A fixed cost is charged for each period the item sits in inventory.

The goal is to find a production schedule — deciding in which period each order is produced — that minimises the total of all changeover and inventory costs, while ensuring every order is completed no later than its due date.

This problem corresponds to **CSPlib Problem 58**: <http://www.csplib.org/Problems/prob058/>

## Parameters

| Parameter           | Description                                                               |
| ------------------- | ------------------------------------------------------------------------- |
| `nb_item_types`     | Number of distinct item types that can be produced                        |
| `nb_orders`         | Total number of orders to be fulfilled (one unit each)                    |
| `nb_periods`        | Number of production time periods available                               |
| `inventory_cost`    | Cost per period for holding one completed order in inventory              |
| `due_period[o]`     | The latest period by which order `o` must be produced                     |
| `change_cost[i, j]` | The setup cost of switching from producing item type `i` to item type `j` |
| `nb_of_orders[t]`   | The number of orders that require item type `t`                           |
| `item_type[o]`      | The item type required by order `o` (0 = idle, i.e. no order)             |

## Decision Variables

| Variable                    | Description                                                                                                                                                      |
| --------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `production_by_order[p]`    | The order produced in period `p`; a value of 0 means the machine is idle in that period                                                                          |
| `production_period[o]`      | The period in which order `o` is produced                                                                                                                        |
| `inventory_periods[o]`      | The number of periods order `o` spends in inventory before its due date (i.e. `due_period[o] - production_period[o]`)                                            |
| `change_cost_for_period[p]` | The changeover cost incurred when moving from period `p` to period `p+1`                                                                                         |
| `production_order[p]`       | The most recently produced (non-idle) order up to and including period `p`; used to determine which item types are adjacent in the schedule for costing purposes |

## Objective

Minimise the **total cost**, which is the sum of:

- All changeover costs across consecutive periods, and
- All inventory holding costs across all orders.

$$\text{minimise} \quad \sum_{p=1}^{T-1} \texttt{change\_cost\_for\_period}[p] \;+\; \texttt{inventory\_cost} \times \sum_{o \in \text{Orders}} \texttt{inventory\_periods}[o]$$

## Constraints

- Each order is produced exactly once; remaining periods are idle.
- No order may be produced after its due date.
- The `production_period` variables are consistent with the `production_by_order` schedule.
- Inventory periods are derived from the difference between an order's due date and its actual production period.
- Changeover costs are assigned according to the sequence in which item types appear in the schedule (idle periods are skipped when determining adjacent item types).
- **Symmetry breaking**: among multiple orders for the same item type, the model fixes them to be produced in a predefined order (earlier orders produced first), since swapping them yields an equivalent solution.

## Instance Data

The included data files (`pigment15a–d`, `pigment20a–c`, `pigment30a–c`) are instances involving pigment manufacturing, a motivating application for this problem class. The numeric suffix indicates the number of orders in the instance.

## References

- CSPlib Problem 058 — Discrete Lot Sizing: <http://www.csplib.org/Problems/prob058/>
- Rendl, A. (2019). MiniZinc CP model for Discrete Lot Sizing. Satalia. (MIT License)
- Drexl, A., & Kimms, A. (1997). Lot sizing and scheduling — Survey and extensions. _European Journal of Operational Research_, 99(2), 221–235.
- Haase, K., & Kimms, A. (2000). Lot sizing and scheduling with sequence-dependent setup costs and times and efficient rescheduling opportunities. _International Journal of Production Economics_, 66(2), 159–169.

## Model update summary

Added concise inline comments in lot_sizing_cp.mzn to clarify:

- production and inventory decision variable roles,
- objective composition (setup plus holding costs),
- optimization direction for minimum total planning cost.
