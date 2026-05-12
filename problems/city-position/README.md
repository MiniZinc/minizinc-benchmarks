# City Position

## Problem Description

Given a set of cities and a (possibly incomplete) table of known distances between pairs of them, this problem asks: **where on a 2D map should each city be placed so that the map distances best match the given real-world distances?**

This is closely related to the classical **Multidimensional Scaling (MDS)** technique used in data visualisation, where high-dimensional data (pairwise distances) are projected onto a lower-dimensional space (a 2D map). Unlike standard MDS, this formulation works with integer coordinates and does not require all pairwise distances to be known — some pairs may be absent from the input.

The specific instances provided use Japanese cities (e.g. Tokyo, Hokkaido, Okinawa, Gifu, Chiba), with distances representing approximate real-world separations.

## Variables

| Variable    | Meaning                                                      |
| ----------- | ------------------------------------------------------------ |
| `x[i]`      | The horizontal (east–west) coordinate of city `i` on the map |
| `y[i]`      | The vertical (north–south) coordinate of city `i` on the map |
| `objective` | The total placement error (see Objective below)              |

All coordinates are integers in the range `[0, max_distance]`, where `max_distance` is the largest distance value in the input.

## Parameters

| Parameter    | Meaning                                                |
| ------------ | ------------------------------------------------------ |
| `N`          | Number of cities                                       |
| `name`       | Array of city names (one per city)                     |
| `R`          | Number of known pairwise distances                     |
| `from`, `to` | Indices of the two cities in each distance pair        |
| `distance`   | Known distance between city `from[i]` and city `to[i]` |

## Distance Approximation

Computing true Euclidean distance $\sqrt{(x_1-x_2)^2 + (y_1-y_2)^2}$ is difficult in integer constraint programming because of the square root. Instead, the model uses a fast integer approximation:

$$\text{approx\_distance}(x_1, y_1, x_2, y_2) = 1007 \cdot \max(|dx|, |dy|) + 441 \cdot \min(|dx|, |dy|)$$

where $dx = x_1 - x_2$ and $dy = y_1 - y_2$. This formula avoids square roots while closely approximating the true Euclidean distance. It is based on a well-known technique described at [flipcode.com](http://www.flipcode.com/archives/Fast_Approximate_Distance_Functions.shtml).

Because of this approximation, all distances in the objective are scaled by **1024** (i.e. the given distances are multiplied by 1024 before comparison), so that the comparison is between `distance[i] * 1024` and the integer approximate distance.

## Objective

Minimise the total absolute error between the given distances and the approximate map distances:

$$\text{objective} = \sum_{i=1}^{R} \left| \text{distance}[i] \times 1024 - \text{approx\_distance}(x[\text{from}[i]],\ y[\text{from}[i]],\ x[\text{to}[i]],\ y[\text{to}[i]]) \right|$$

A smaller objective means the computed map layout is a better fit for the given distances.

## Symmetry Breaking

Without additional constraints, many equivalent solutions exist (e.g. the map could be rotated or reflected). The model fixes the solution orientation using three anchor cities:

- **Hokkaido** (second-to-last city): placed at the maximum `y` value — i.e. at the top of the map.
- **Okinawa** (last city): fixed at the origin `(0, 0)`.
- **Chiba** (third-to-last city): required to be to the right of the midpoint between Hokkaido and Okinawa.

These constraints reflect the approximate real geography of Japan, and are hardcoded into the model. This means the model is **specific to instances that include Hokkaido, Chiba, and Okinawa as the last three cities** (in that order). Instances with different cities may need these constraints adjusted.

## Notes

- This model appears to be an original formulation rather than one published in a specific academic paper. If a reference is known, it would be worth adding here.
- The symmetry-breaking constraints are tied to specific named cities (Hokkaido, Chiba, Okinawa) by their positions in the array rather than by name matching. Care should be taken when adding new instances to ensure city ordering matches these assumptions.

## Model update summary

Added concise inline comments in city-position.mzn to clarify:

- coordinate decision variables x and y as map placements,
- objective bound construction for safe error-domain sizing,
- objective meaning as total absolute distance mismatch.
