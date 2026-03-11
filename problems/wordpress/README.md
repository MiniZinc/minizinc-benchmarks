# Wordpress Deployment Optimisation (MiniZinc)

## What problem is this model solving?

This model chooses how to deploy a Wordpress-based web stack onto virtual machines (VMs) at minimum total cost.

You can think of it as a **cloud placement problem**:
- there are application components (Wordpress, MySQL, load balancers, Varnish),
- there are candidate VM types with different capacities and prices,
- and the model decides where to place each component while respecting technical rules.

The final goal is to get a valid architecture that is as cheap as possible.

## Main inputs (data you provide)

- `VM`: maximum number of VM slots available.
- `NoComponents`: number of software components.
- `HardwareREQ`: number of resource dimensions (for example CPU/RAM/storage).
- `CompREQ[i,h]`: resource need of component `i` on resource `h`.
- `VMOffers`: number of available VM types.
- `VMSpecs[v,h]`: capacity of VM type `v` on resource `h`.
- `VMPrice[v]`: price of VM type `v`.
- `WPInstances`: required minimum number of Wordpress instances.

## Decision variables (what the solver chooses)

- `AssignmentMatrix[i,k] in {0,1}`: whether component `i` is deployed on VM `k`.
- `OccupancyVector[k] in {0,1}`: whether VM `k` is used at all.
- `VMType[k]`: which VM offer/type is selected for VM `k`.
- `Price[k]`: effective cost of VM `k` (0 when unused, VM price when used).

## Key constraints (rules the solution must satisfy)

- **Basic deployment**: most components must be deployed at least once.
- **Capacity feasibility**: total assigned component demand on each VM must not exceed that VM type’s capacity.
- **Usage/cost linking**: used VMs must be marked occupied; VM price depends on selected type and occupancy.
- **Wordpress architecture rules**:
  - DNS and HTTP load balancers are mutually exclusive.
  - Wordpress must be supported by a load balancer (ratio depends on which LB type is active).
  - Wordpress and MySQL have a required provide/require relationship.
- **Conflict rules**: some components cannot be co-located on the same VM (e.g., Varnish conflicts with several others).
- **Instance bounds**:
  - at least `WPInstances` Wordpress instances,
  - at least 2 Varnish,
  - at least 2 MySQL,
  - at most 1 DNS load balancer.

## Objective

The model minimizes total deployment cost:

`objective = sum(k in 1..VM)(Price[k])`

So among all valid deployments, it prefers the cheapest combination of VM usage and VM types.

## Uncertainty and modeling notes

- Component IDs are hard-coded (`Wordpress=1`, `MySQL=2`, etc.), so correctness depends on the input data using the same indexing convention.
- The model encodes several domain-specific ratios (for load balancer support and Wordpress↔MySQL relations); without external business documentation, those are interpreted as given requirements rather than universally valid architecture rules.
- Input files likely represent synthetic or benchmark scenarios, so real cloud pricing/performance details may differ.

## References (identifiable from repository/model)

- Model source: `todo/working/wordpress/wordpress.mzn`
- Original/curated benchmark copy: `problems/wordpress/wordpress.mzn`
- Existing benchmark description: `problems/wordpress/README.md`
- Metadata/challenge entry: `problems/wordpress/metadata.json` (MiniZinc Challenge 2022 data listed)
- In-file attribution comments mention Andrei Iovescu (original model design) and Bogdan David (adaptation).
