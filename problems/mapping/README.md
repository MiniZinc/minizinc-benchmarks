# Application Mapping on Network-on-Chip (NoC)

## Problem Description

This model addresses the problem of **mapping streaming applications onto multiprocessor systems** connected by a Network-on-Chip (NoC). The goal is to decide which processor each computational task (called an _actor_) should run on, while minimising the combined cost of computation and communication across all processors.

The motivating application is the H.263 video encoder (and similar streaming workloads such as MP3 decoding), which can be decomposed into a set of actors that communicate data streams with each other. These actors must be placed on the processors of a chip in a way that balances the workload and keeps communication overhead low.

This model is a simplified version of the one described in:

> Usman Mazhar Mirza, Flavius Gruian, and Krzysztof Kuchcinski.
> "Mapping streaming applications on multiprocessors with time-division-multiplexed network-on-chip."
> _Computers & Electrical Engineering_, vol. 40, no. 8, pp. 276–291, 2014.

---

## System Architecture

The hardware platform is a **rectangular mesh of processors** with `row` rows and `col` columns, giving `k = row × col` processors in total. Processors are connected by directional links that form the NoC. Each link has a fixed bandwidth limit (`link_bandwidth`).

Data instances (supplied in `.json` files) represent various mesh sizes (2×2, 3×3, 4×4) and topologies (full mesh, ring, star) running different streaming applications (H.263/MPEG encoder, MP3 decoder).

---

## Parameters

| Parameter                  | Meaning                                                              |
| -------------------------- | -------------------------------------------------------------------- |
| `row`, `col`               | Dimensions of the processor mesh                                     |
| `k`                        | Total number of processors (`row × col`)                             |
| `no_links`                 | Number of directed links between processors                          |
| `no_flows`                 | Number of data flows (communications) between actors                 |
| `no_actors`                | Number of actors (computational tasks) in the application            |
| `link_bandwidth`           | Maximum data rate on a single NoC link                               |
| `actor_load`               | Computational load imposed by each actor                             |
| `processor_load`           | Maximum allowable load on a single processor                         |
| `arc`                      | Description of the network topology (which nodes each link connects) |
| `inStream`                 | Data rate (stream size) for each flow                                |
| `source_destination_actor` | For each flow, identifies the source actor and the destination actor |
| `balance`                  | Flow conservation values at each network node for each flow          |

---

## Decision Variables

| Variable                        | Meaning                                                                                                    |
| ------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `flow_processor[1..2*no_flows]` | For each flow, the processor assigned to its source actor (first half) and destination actor (second half) |
| `actor_processor[1..no_actors]` | The processor assigned to each actor (derived from `flow_processor`)                                       |
| `inFlow[i, j]`                  | Amount of flow `i` entering the network at processor `j`                                                   |
| `outFlow[i, j]`                 | Amount of flow `i` leaving the network at processor `j`                                                    |
| `commFlow[i, l]`                | Amount of flow `i` traversing link `l` in the NoC                                                          |
| `cpu_loads[j]`                  | Total computational load placed on processor `j`                                                           |
| `cost[i]`                       | Communication cost (total link usage) for flow `i`                                                         |
| `communication_cost`            | Overall communication cost across all flows                                                                |
| `objective`                     | The value being minimised (see below)                                                                      |

---

## Constraints

1. **No flow splitting**: Each data flow is either fully routed through a processor or not at all — a flow cannot be split across multiple processors.

2. **Single source and sink per flow**: Each flow originates at exactly one processor and terminates at exactly one processor, corresponding to the assigned processors for its source and destination actors.

3. **Network flow conservation**: For every flow and every node in the network, the amount of data entering equals the amount leaving (except at the source and sink nodes). This is enforced using the `network_flow_cost` global constraint.

4. **Link bandwidth**: The total data routed over any single link must not exceed its bandwidth capacity.

5. **Processor load**: The total computational load assigned to each processor (captured via bin packing) must not exceed the processor's capacity.

6. **Actor consistency**: If the same actor appears as the source (or destination) of multiple flows, it must be mapped to the same processor in all cases.

---

## Objective

The model minimises the **maximum over all processors** of the sum of:

- the processor's **CPU load** (from the actors assigned to it), and
- the **communication cost** of all flows originating at that processor.

$$\text{minimise} \quad \max_{j=1}^{k} \left( \text{cpu\_loads}[j] + \text{cc}[j] \right)$$

This objective encourages both load balancing (no single processor is overloaded) and locality of communication (actors that communicate heavily are preferably placed close together or on the same processor).

---

## Notes

- The model uses the MiniZinc global constraints `network_flow_cost` and `bin_packing_load`.
- The network is modelled with two virtual "super-nodes" (source and sink) appended to the `k` physical processors, giving `n = k + 2` nodes in total.
- The model was authored by Krzysztof Kuchcinski.

## Model update summary

Added concise inline comments in mapping.mzn to clarify:

- actor/flow assignment variable roles,
- objective semantics as max processor load-plus-communication,
- minimization intent for balanced NoC mapping.
