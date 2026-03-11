# Gamete Breeding Optimisation

## Problem Description

This model addresses a problem from **plant breeding**: given a collection of starting gametes (haploid genetic sequences), find the minimum number of crossing operations needed to produce a desired target gamete.

In genetics, a **gamete** is a haploid cell (carrying one copy of each chromosome). Each gamete is represented here as a binary string over a fixed number of **loci** (positions on a chromosome). A value of `1` at a locus means the "favourable" allele is present; a `0` means it is absent. The **target gamete** is the ideal plant, which has the favourable allele (`1`) at every locus.

Gametes can be bred together through **crossing (recombination)**: two parent gametes are combined by taking segments from each parent, switching between them at most `maxCrossovers` times along the chromosome. The result is a new gamete that inherits pieces of both parents.

The question is: starting from a given set of donor gametes, what is the fewest number of crossings required to breed the target gamete?

## Model Structure

The breeding plan is represented as a **binary tree**:

- **Leaves** correspond to donor gametes from the available pool.
- **Internal nodes** represent a single crossing event between two child gametes, producing a new gamete at that node.
- The **root** (cell 1) must yield the all-`1`s target gamete.

The tree is stored as a flat array of `nTreeCells` cells. Each cell can be one of three types:

| Type   | Meaning                                              |
| ------ | ---------------------------------------------------- |
| `Leaf` | A starting donor gamete, assigned from the input set |
| `Node` | An internal crossing between two child cells         |
| `Null` | An unused (empty) slot in the tree                   |

The model enforces that the tree is well-formed: children always have larger indices than their parent, and the root must produce the target.

## Parameters

| Parameter       | Description                                                                     |
| --------------- | ------------------------------------------------------------------------------- |
| `nLoci`         | Number of genetic loci (length of each gamete sequence)                         |
| `nGametes`      | Number of available donor gametes                                               |
| `gametes`       | A 2-D binary array giving the allele values for each donor gamete at each locus |
| `maxCrossovers` | Maximum number of crossover points allowed in a single crossing event           |
| `nTreeCells`    | Size of the tree (an upper bound on the breeding plan depth/width)              |

## Decision Variables

| Variable                      | Description                                                                       |
| ----------------------------- | --------------------------------------------------------------------------------- |
| `treeType[i]`                 | Type of tree cell `i` — `Node`, `Leaf`, or `Null`                                 |
| `treeLeft[i]`, `treeRight[i]` | Indices of the left and right children of cell `i` (0 if not a node)              |
| `xs[i, j]`                    | Allele value (0 or 1) at locus `j` produced at tree cell `i`                      |
| `index[i]`                    | For leaf cells: which donor gamete is assigned to cell `i` (0 if not a leaf)      |
| `source[i, j]`                | For cell `i` at locus `j`: which parent (1 = left, 2 = right) provides the allele |
| `swap[i, j]`                  | Whether a crossover occurs between loci `j-1` and `j` at cell `i`                 |

## Constraints

- **Tree validity**: Parent cells have smaller indices than their children; every internal node has two non-null children.
- **Leaf assignment**: Each leaf is assigned a unique donor gamete, and its allele values match that gamete exactly.
- **Crossing rule**: At each internal node, the offspring gamete is assembled from the two parent gametes by selecting alleles locus by locus, with the number of switches between parents limited to `maxCrossovers`.
- **Target**: The gamete at the root (cell 1) must be all `1`s.
- **Symmetry breaking**: Redundant solutions that are equivalent under tree symmetry are excluded.

## Objective

**Minimise** the number of internal `Node` cells in the breeding tree — i.e., find the breeding plan that achieves the target gamete using as few crossing operations as possible.

## Notes

This model appears to have been written by Kelvin Davis (2023). The problem is related to the field of **marker-assisted gene pyramiding** in plant breeding, which seeks efficient strategies for combining multiple favourable alleles into a single variety. Relevant background can be found in:

- Servin, B., Martin, O. C., Mézard, M., & Hospital, F. (2004). "Toward a Theory of Optimal Marker-Assisted Gene Pyramiding." _Genetics_, 168(1), 513–523.

If you are aware of a more specific publication associated with this exact formulation, please update this reference.
