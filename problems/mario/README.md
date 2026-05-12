# Mario's Neighbourhood Route

## Problem Description

Mario is an Italian plumber who spends his days visiting the houses in his neighbourhood to collect gold coins hidden in the plumbing. Each morning he sets off from his own house and must finish his day at his friend Luigi's house for supper. Mario travels by kart, which carries a fixed amount of fuel.

The goal is to plan the **best route** for Mario — choosing which houses to visit and in what order — so that he **collects as many gold coins as possible** without running out of fuel.

From a graph perspective, this is a **constrained path problem**:

- The neighbourhood is modelled as a directed graph where each house is a node.
- The road between any two houses has a known fuel consumption (arc weight).
- Each house contains a known number of gold coins (node weight).
- The route must start at Mario's house and end at Luigi's house.
- The total fuel used must not exceed the kart's fuel capacity.
- The objective is to maximise the total gold coins collected along the route.

Not every house needs to be visited; Mario picks the most profitable subset of houses that fits within his fuel budget.

This problem is related to the **Prize-Collecting Traveling Salesman Problem (PC-TSP)**, where a traveller selects a profitable subset of locations to visit subject to a resource constraint.

## Parameters

| Parameter         | Description                                                                                 |
| ----------------- | ------------------------------------------------------------------------------------------- |
| `nbHouses`        | Total number of houses in the neighbourhood (including Mario's and Luigi's)                 |
| `MarioHouse`      | Index of Mario's house (the route start)                                                    |
| `LuigiHouse`      | Index of Luigi's house (the route end)                                                      |
| `fuelMax`         | Maximum fuel available in the kart                                                          |
| `goldTotalAmount` | Total gold available across all houses (used as an upper bound)                             |
| `conso`           | 2D array: `conso[i,j]` is the fuel consumed travelling directly from house `i` to house `j` |
| `goldInHouse`     | Array: `goldInHouse[i]` is the number of gold coins at house `i`                            |

## Decision Variables

| Variable    | Description                                                                                                                                              |
| ----------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `succ`      | Array of successor variables. `succ[i]` is the next house visited after house `i`. If `succ[i] = i`, house `i` is **not** on the route (Mario skips it). |
| `fuel`      | Total fuel consumed along the chosen route.                                                                                                              |
| `objective` | Total gold coins collected (the value to be maximised).                                                                                                  |

## How the Route is Encoded

The route is represented using **successor variables**: `succ[i]` gives the house Mario visits immediately after house `i`. Houses that Mario does not visit are given a self-loop (`succ[i] = i`), effectively removing them from the route.

The global constraint `subcircuit(succ)` ensures that the visited houses form a single valid path (no branching, no disconnected segments). By additionally fixing `succ[LuigiHouse] = MarioHouse`, the circuit is broken into a directed path that starts at Mario's house and ends at Luigi's house.

## Objective

Maximise the total gold coins collected:

$$\text{objective} = \sum_{i=1}^{\texttt{nbHouses}} \mathbb{1}[\texttt{succ}[i] \neq i] \times \texttt{goldInHouse}[i]$$

subject to:

$$\sum_{i=1}^{\texttt{nbHouses}} \texttt{conso}[i][\texttt{succ}[i]] \leq \texttt{fuelMax}$$

## Instance Details

Instances vary in size and difficulty (easy, medium, hard) based on the number of houses and the tightness of the fuel constraint. This problem was featured in the **MiniZinc Challenge** competitions in 2013 and 2014.

## Authors

Amaury Ollagnier, Jean-Guillaume Fages

## Model update summary

Added concise inline comments in mario.mzn to clarify:

- successor/path decision variable semantics,
- objective interpretation as collected gold,
- optimization direction under fuel constraints.
