# Service Function Chaining (SDN-Chain)

## Problem Description

Modern networks often virtualise their services as **Virtual Network Functions (VNFs)** — software implementations of things like firewalls, VPN tunnels, traffic shapers, and deep-packet inspectors. A **Service Function Chain (SFC)** is an ordered sequence of such functions that network traffic must traverse, for example: `ENDPOINT → DPI → NAT → VPN → ENDPOINT`.

In this problem the network is divided into multiple **domains** (administrative regions), each containing a set of VNF nodes interconnected by links. The challenge is to find a valid deployment of a given SFC — that is, to assign each required VNF in the chain to a physical node in the network and select the inter-domain links that connect them — while minimising the total cost of crossing domain boundaries.

This is an **optimisation** problem from Software-Defined Networking (SDN) research.

## Input Data

| Parameter | Description |
|---|---|
| `n_nodes`, `n_domains` | Total VNF nodes and administrative domains |
| `nodes` | Attributes of each node (type, domain, state flags, etc.) |
| `node_links` | Directed links between nodes |
| `domain_link_weights` | Cost matrix for inter-domain gateway links |
| `vnflist` | The ordered sequence of VNF types the chain must visit |
| `vnf_arcs` | Arcs between consecutive entries in the VNF list |
| `start_domain`, `target_domain` | Source and destination domains for the chain |
| `domain_constraints` | Per-domain limits on how many VNFs of each type may be used |
| `proximity_to_source/destination` | Flags requiring certain VNFs to be placed in the source or target domain |

Instance files are named `dXXnYYY.dzn`, where a higher `XX` indicates greater difficulty and, for equal `XX`, a higher `YYY` also indicates a harder instance.

## Decision Variables

| Variable | Meaning |
|---|---|
| `vnf_match[i]` | Which physical node hosts the *i*-th VNF in the chain |
| `link_selection[i]` | Whether link *i* is active (1) or not (0) in the solution |
| `selected_nodes[i]` | Whether node *i* is part of the solution |
| `selected_domain[i]` | Whether domain *i* is traversed by the chain |
| `domain_path[i,j]` | Whether domain *i* is reachable from domain *j* via selected links |
| `n_fun_nodes` | Count of functional (non-gateway) nodes selected |

## Key Constraints

- **Type matching**: each position in the VNF chain must be assigned to a node whose type matches the required service (DPI, NAT, VPN, WAN accelerator, shaper, etc.).
- **Endpoint anchoring**: the chain starts and ends at designated `ENDPOINT` nodes in the source and target domains.
- **Domain reachability**: selected domains must form a valid, acyclic path from source to target — each intermediate domain has exactly one incoming inter-domain link; loops are forbidden.
- **Domain-level quotas**: `domain_constraints` limits how many VNFs of a given type may be deployed within each domain.
- **Proximity**: certain VNFs may be required to be placed in the source or destination domain.
- **Consistency**: `selected_nodes`, `selected_domain`, and `link_selection` are kept mutually consistent.

## Objective

Minimise the **total weighted cost of selected inter-domain gateway links**:

$$\text{objective} = \sum_{\text{selected gateway-to-gateway links}} \text{domain\_link\_weights}[d_1, d_2]$$

Lower cost means the SFC is deployed along cheaper (e.g., shorter or less congested) inter-domain paths.

## Notes on Uncertainty

The model is parameterised; the actual network topology, VNF placements, service chain specification, and domain constraints all come from the data file. Instance difficulty is encoded in the filename (`dXX` prefix), but the exact mapping to structural properties (number of domains, chain length, density of constraints) is not documented within the model itself.

## Reference

Liu, Tong, et al. "Constraint programming for flexible Service Function Chaining deployment." *arXiv preprint* [arXiv:1812.05534](https://arxiv.org/abs/1812.05534) (2018).
