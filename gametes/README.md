# Gametes Crossing Tree Model

## Overview

This MiniZinc model represents a **genetic crossing problem** where we aim to construct a tree of gametes (haploid genetic sequences) to produce a desired plant genotype. The tree simulates how gametes combine through crossover events to generate new genetic combinations. The objective is to minimise the number of internal nodes (crossing events) required to achieve the target genotype.

---

## Problem Description

- We are given:
  - A set of **gametes** (binary sequences representing genetic loci).
  - A maximum number of allowed **crossovers** during recombination.
  - A desired genotype that must appear at the root of the tree.
- The tree consists of:
  - **Leaf nodes**: Represent original gametes.
  - **Internal nodes**: Represent new gametes created by crossing two child nodes.
  - **Null nodes**: Empty placeholders.

The challenge is to build a valid tree structure that respects genetic recombination rules and produces the target genotype at the root.

---

## Key Parameters

- `nLoci`: Number of genetic loci (positions in the sequence).
- `nGametes`: Number of available gametes.
- `maxCrossovers`: Maximum allowed crossover points in a recombination.
- `nTreeCells`: Maximum number of nodes in the tree.

### Sets

- `NLoci`: Indices for loci (1..nLoci).
- `NGametes`: Indices for gametes (1..nGametes).
- `NTreeCells`: Indices for tree nodes (1..nTreeCells).

---

## Decision Variables

- `treeType[i]`: Type of node `i` (`Node`, `Leaf`, or `Null`).
- `treeLeft[i]`, `treeRight[i]`: Indices of left and right child nodes for internal nodes.
- `index[i]`: Gamete index for leaf nodes (0 if not assigned).
- `xs[i,j]`: Genetic sequence at node `i` for locus `j` (binary value).
- `source[i,j]`: Indicates which parent contributes the allele at locus `j` (1 or 2).
- `swap[i,j]`: Indicates crossover points (0 or 1).

---

## Constraints

1. **Tree Structure**:
   - Internal nodes have two valid children.
   - Leaf nodes link to original gametes.
   - Null nodes have no children and all loci set to 0.
2. **Genetic Rules**:
   - Internal nodes combine alleles from two parents.
   - Number of crossovers per recombination ≤ `maxCrossovers`.
3. **Target Genotype**:
   - The root node (node 1) must match the desired genotype (all loci = 1).
4. **Uniqueness**:
   - Leaf nodes use distinct gametes.
5. **Symmetry Breaking**:
   - Avoid equivalent tree structures by enforcing dominance constraints.

---

## Objective

Minimise:
\[
\text{objective} = \text{count of internal nodes (crossing events)}
\]
This ensures the simplest possible crossing tree to achieve the target genotype.

---

## Notes

- This model is useful for **plant breeding**, **genetic algorithm design**, and **bioinformatics**.
- It demonstrates how constraint programming can model biological processes like recombination.

---
