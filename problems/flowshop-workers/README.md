# Flowshop Workers

## Overview

This MiniZinc model schedules products through a sequence of manufacturing stations while also assigning the required manual work to a limited number of workers.

Each product moves through the stations in the same order, like a classic flow shop. Some stations are purely manual, while others are partly automatic: a worker may need to perform a setup task, the machine then runs automatically for some time, and finally a worker may need to return for a takedown task. Workers are not tied to one station, so the model must also account for the time needed for a worker to walk from one station to another.

The goal is to build a feasible production plan that respects product order, worker availability, travel times, release times, and limited buffer space between stations.

## What the model decides

The model chooses:

- when each product starts its work at each station,
- which worker performs each manual task,
- when each assigned worker starts that task,
- and therefore when the final product finishes the last required station.

Two families of decision variables are central:

- `proST[product, station, workstep]`: the start time of a product workstep at a station,
- `workST[product, station, workstep, worker]`: the start time of the same workstep if it is assigned to a particular worker.

These are optional start times, which means a task can be absent when it is not needed. This is important because some products may already be partway through production, and some stations only require one manual intervention while others require two.

## Meaning of the data

The main input data describes the factory state:

- `numberWorkers`, `numberStations`, `numberProducts`, `numberProductTypes`: problem size,
- `productionTimeMatrix`: machine processing time for each product type at each station,
- `setupTimes` and `takedownTimes`: manual times around automatic processing,
- `numberManualWorksteps`: whether a station needs one manual step or two,
- `workerMovementMatrix`: walking time between stations,
- `workerInitial` and `releaseTimeW`: each worker's starting location and availability time,
- `releaseTime`: the earliest time a product may continue,
- `currentStation`, `currentStep`, `currentBuffer`: where each product currently is when scheduling begins,
- `productType`: the type of each product.

In effect, the model can start from a partially completed shop floor state rather than assuming every product begins at the first station.

## Main rules captured by the model

At a high level, the schedule must satisfy the following:

- **Flow order:** every product visits stations in increasing order.
- **Queue order:** products keep their relative order through the line.
- **Single assignment of manual work:** each required manual workstep is carried out by exactly one worker.
- **Worker travel:** if a worker performs two tasks at different stations, enough time must be left for finishing the first task and walking to the next one.
- **Worker initial position:** a worker cannot begin a task before reaching its station from the worker's starting position.
- **Automatic stations:** when a station has two manual worksteps, the second one is forced to occur after the machine's automatic processing time.
- **Limited buffers:** the model prevents more than one product from occupying the same intermediate buffer at once.
- **Release times and partial progress:** products and workers may already be busy or delayed when the schedule starts, and the model respects that status.

## Objective

The model minimizes `objective`, which is the completion time of the last required workstep of the last product at the last station.

In plain terms, it tries to **finish the overall production line as early as possible**.

## Notes and uncertainties

A few details are inferred from the constraint comments rather than fully documented in the model itself:

- `currentStep` appears to encode the exact stage a product has already reached at its current station.
- The meanings of values `2`, `3`, and especially `4` can be partly inferred from comments, but the full business interpretation is not explicitly documented in the file.
- The model assumes products are already ordered in queue position by their index.

If this benchmark is to be reused or extended, those state conventions would benefit from a short data-format note.

## Related literature

I could not confidently identify the exact paper from which this benchmark was derived.

A closely related line of work studies flow-shop scheduling with a limited human resource that performs setup and removal tasks around machine processing, for example:

- T.C. Edwin Cheng, Guoqing Wang, and Chelliah Sriskandarajah, _One-operator–two-machine flowshop scheduling with setup and dismounting times_, Computers & Operations Research, 26(7), 1999, pp. 715–730. DOI: 10.1016/S0305-0548(98)00087-2.

## Model update summary

Added concise inline comments in flowshop-workers.mzn to clarify:

- core optional-interval scheduling variables,
- objective expression as final completion time,
- documentation-only nature of the update.

That paper is more specialized than this benchmark, but it addresses the same broad idea of combining flow-shop timing with worker-operated setup/takedown activities.
