# Zephyrus 2016 — Cloud Application Deployment

## Problem Description

This model solves the **cloud component deployment** problem: given a set of software
components and a set of cloud locations (e.g. virtual machines or servers), decide how
many instances of each component to deploy and on which locations, so that all
inter-component dependencies are satisfied and the total hosting cost is minimised.

Software components interact through **ports**. A component can *require* a certain
number of connections on a port (e.g. a web frontend requires three database connections)
and can *provide* connections on a port, either up to a fixed capacity or with unlimited
capacity. The model tracks the exact number of **bindings** — directed connections between
a providing component instance and a requiring component instance — to ensure every
requirement is fully satisfied without overloading any provider.

Additionally, some pairs of components are declared **conflicting** on a port: if a
providing component is involved in a conflict, it must not coexist on the deployment with
the conflicting requiring component (or it may only be deployed as a single instance).

Each location has a fixed set of **resource capacities** (e.g. CPU cores, memory) and a
**cost**. Components consume resources, so the total resource consumption of components
placed on a location must not exceed that location's capacity.

The goal is to find a valid deployment that **minimises the total cost** of all used
locations.

## Sets and Parameters

| Name | Description |
|------|-------------|
| `comps` | Set of component types |
| `ports` | Set of port types (dependency edges) |
| `multi_provide_ports` | Subset of ports that use multi-provide semantics |
| `locations` | Set of candidate cloud locations |
| `resources` | Set of resource types (e.g. CPU, RAM) |
| `requirement_port_nums` | How many bindings each component requires per port |
| `provide_port_nums` | How many bindings each component can provide per multi-port (`-1` = unlimited) |
| `conflicts` | Whether a component conflicts on a given port |
| `costs` | Cost of each location when used |
| `resource_provisions` | Resources available at each location |
| `resource_consumptions` | Resources consumed by each component instance |

## Decision Variables

| Variable | Description |
|----------|-------------|
| `comps_num[c]` | Total number of instances of component `c` to deploy |
| `comp_locations[l, c]` | Number of instances of component `c` placed at location `l` |
| `used_locations[l]` | 1 if location `l` is used, 0 otherwise |
| `bindings[mport, port, pcomp, rcomp]` | Number of connections from providing component `pcomp` to requiring component `rcomp` through multi-provide port `mport` for dependency port `port` |
| `objective` | Total deployment cost (sum of costs of used locations) |

## Objective

Minimise the total cost of used locations:

$$\text{objective} = \sum_{l \in \text{locations}} \text{used\_locations}[l] \times \text{costs}[l]$$

## Key Constraints

- **Requirement satisfaction**: every instance of a requiring component must receive
  exactly the number of bindings its port requirement demands.
- **Provider capacity**: the total bindings served by a provider instance must not exceed
  its declared capacity (or any amount if the capacity is unlimited, as long as at least
  one instance exists).
- **Conflict**: conflicting component pairs cannot coexist in the deployment (or the
  provider is restricted to a single instance).
- **Unicity**: a component cannot be both the sole provider and sole recipient of a
  binding to itself beyond what is numerically feasible.
- **Resource capacity**: the aggregate resource consumption of all components placed at a
  location must not exceed that location's resources.
- **Symmetry breaking**: when two locations have identical resource profiles, a
  lexicographic ordering on component assignments is enforced to reduce symmetric
  solutions.

## Notes and Uncertainty

- The model encodes the **Zephyrus** cloud configurator problem, originally developed at
  INRIA/University of Bologna. Some data files may include hard-wired instance-specific
  constraints (see the bottom of the model file) that reflect a particular benchmark
  scenario rather than the general problem.
- The parameter `provide_port_nums = -1` encodes **infinite capacity** providers; the
  model handles this case separately from bounded providers.
- The constant `MAX_INT = 4096` acts as a practical upper bound on instance counts and
  binding counts; whether this is sufficient depends on the specific data instance.

## References

- Jacopo Mauro (2016) — model author and copyright holder (ISC Licence).
- Zephyrus tool: Eyk Bernhard, et al., *"Zephyrus: Optimal Deployment of Component-Based
  Cloud Applications"*, and subsequent work at INRIA/Université Paris Diderot on
  automated component configuration.
- For the Zephyrus problem formulation see also: Mauro, J., Nieke, M., Sartori, C., Yu,
  I. C., *"Context Aware Reconfiguration in Component Based Systems"*, NordCloud / SCASE
  workshops (2015–2016).

## Model update summary

Added concise inline comments in zephyrus.mzn to clarify:

- component, binding, and location decision variable semantics,
- dependency and resource feasibility constraints,
- objective intent as minimizing deployment location cost.
