# MiniZinc Model: Wordpress Deployment Optimisation

## **Overview**

This MiniZinc model addresses the problem of **deploying a Wordpress-based application architecture onto virtual machines (VMs)** in a cost-efficient manner. The goal is to allocate application components (such as Wordpress, MySQL, load balancers, and caching services) to a set of VMs while satisfying hardware requirements and deployment constraints, and minimising the total cost of the infrastructure.

---

## **Problem Description**

The application consists of multiple components, each with specific hardware requirements (CPU, memory, storage). There are several VM offers available, each with defined specifications and pricing. The model determines:

- Which components are deployed on which VMs.
- The type of VM chosen for each instance.
- The total cost of the deployment.

The solution must respect constraints such as:

- Hardware capacity limits.
- Component-specific deployment rules (e.g., Wordpress requires MySQL).
- Conflict and exclusivity rules between certain components.
- Minimum and maximum instance counts for components.

---

## **Inputs**

- `VM`: Maximum number of virtual machines available.
- `NoComponents`: Number of application components.
- `HardwareREQ`: Number of hardware resource types (e.g., CPU, Memory, Storage).
- `CompREQ[i,h]`: Hardware requirements for component `i` for resource `h`.
- `VMOffers`: Number of VM types available.
- `VMSpecs[v,h]`: Hardware specifications for VM type `v`.
- `VMPrice[v]`: Price for VM type `v`.
- `WPInstances`: Minimum number of Wordpress instances required.

---

## **Decision Variables**

- `AssignmentMatrix[i,k]`: Binary variable indicating if component `i` is deployed on VM `k`.
- `OccupancyVector[k]`: Indicates whether VM `k` is used.
- `VMType[k]`: VM type assigned to VM `k`.
- `Price[k]`: Cost of VM `k` based on its type and occupancy.

---

## **Constraints**

1. **Basic Allocation:**  
   Each component (except specified exclusions) must be deployed at least once.
2. **Occupancy:**  
   VMs that host components must be marked as occupied.

3. **Capacity:**  
   Total resource usage on a VM cannot exceed its specifications.

4. **Linking VM Type and Price:**  
   Price is determined by VM type and occupancy.

5. **Deployment Rules:**

   - Wordpress requires MySQL and a load balancer.
   - DNS and HTTP load balancers cannot be deployed together.
   - Varnish cannot coexist with certain components.

6. **Bounds:**
   - Minimum and maximum number of instances for specific components.
   - Exclusive deployment for certain components.

---

## **Objective**

Minimise:

```minizinc
objective = sum(k in 1..VM)(Price[k]);
```

This represents the total cost of all used VMs.

---

## **Applications**

- Cloud infrastructure optimisation.
- Cost-efficient deployment of web applications.
- Resource allocation in virtualised environments.

---

## **References**

- Inspired by real-world cloud deployment scenarios for Wordpress-based architectures.
- Related concepts: Virtual Machine Placement, Resource-Constrained Scheduling.

---
