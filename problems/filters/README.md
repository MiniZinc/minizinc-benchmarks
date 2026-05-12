# Filters

## Overview

This MiniZinc model describes a **scheduling and resource-assignment problem for filter computations**. The operations in the filter are divided into **additions** and **multiplications**, and the goal is to decide:

- **when** each operation starts, and
- **which hardware resource** performs it,

so that all dependency rules are respected and the full computation finishes as early as possible.

At a high level, this is a classic **resource-constrained scheduling** model from digital hardware design: a filter is represented as a graph of operations, where some operations must wait for others to finish, and only a limited number of adders and multipliers are available.

## Inputs

The model is parameterized by:

- `n`: total number of operations.
- `add`: the set of operations that are additions.
- `mul`: the set of operations that are multiplications.
- `Last`: the set of final operations whose completion determines the overall finishing time.
- `del_add`: duration of an addition.
- `del_mul`: duration of a multiplication.
- `number_add`: number of available adders.
- `number_mul`: number of available multipliers.
- `dependencies[i]`: the set of operations that must occur **after** operation `i`.

The model also includes a small consistency check to ensure that every operation is classified as either an addition or a multiplication, and not both.

## Decision variables

The main decision variables are:

- `t[i]`: the start time of operation `i`.
- `r[i]`: the resource assigned to operation `i`.
  - For additions, this identifies one of the available adders.
  - For multiplications, this identifies one of the available multipliers.
- `d[i]`: the duration of operation `i`, derived from its type.
- `objective`: the overall finishing time of the computation.

## Constraints

The model enforces three main ideas.

### 1. Precedence constraints

If operation `j` depends on operation `i`, then `j` cannot start until `i` has finished:

$$t[i] + d[i] \le t[j]$$

This captures the data flow of the filter.

### 2. Resource limits

Each operation must be assigned to a valid resource of the correct type:

- addition operations can only use one of the `number_add` adders,
- multiplication operations can only use one of the `number_mul` multipliers.

### 3. No overlap on the same resource

Two additions cannot run at the same time on the same adder, and two multiplications cannot run at the same time on the same multiplier.

The model expresses this with the global constraint `diffn`, treating each operation as a rectangle in a time/resource grid:

- horizontal position = start time,
- horizontal size = operation duration,
- vertical position = resource number,
- vertical size = 1.

This is a compact way to state that operations assigned to the same resource must not overlap in time.

## Objective

The model minimizes the completion time of the final operations in `Last`. In scheduling terms, it minimizes the **makespan** of the filter computation.

So the solver looks for a schedule that finishes the full filter as early as possible while using only the available adders and multipliers.

## Output

A solution reports:

- `objective`: the finishing time of the schedule,
- `t`: the start times of all operations,
- `r`: the resource chosen for each operation.

## Interpretation

This model is a good example of how MiniZinc can represent a hardware scheduling problem in a simple, declarative way. The filter itself is not described by equations here; instead, it is represented indirectly through operation types and dependency links.

One detail that may need confirmation from a domain expert is the exact benchmark origin and the precise meaning of the individual instance names such as `fir`, `dct`, `ar`, and `ewf`. They appear to refer to different filter or signal-processing structures, but the model itself only requires their operation graph and resource limits.

## Possible source context

The model header credits **Krzysztof Kuchcinski**, and the benchmark strongly resembles work on **high-level synthesis** and **scheduling of digital signal processing / filter computations** under limited hardware resources.

However, from the repository contents alone, the exact paper or publication source cannot be identified with confidence. If a precise academic reference is needed, another expert should verify the original benchmark provenance before citing a specific publication.

## Model update summary

The model now derives an internal `Operation` enum from the existing `add` and `mul` input sets. That keeps the data format unchanged while making the operation type explicit in the duration and resource-capacity constraints.

In practice, this means the schedule logic now reads in terms of named operation kinds instead of repeated membership checks against raw integer sets.

Targeted inline comments were also added in `filter.mzn` around precedence, resource bounds, `diffn` packing, and makespan computation so the intent of each constraint block is clearer when reading the model top-to-bottom.
