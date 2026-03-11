# Skill Allocation

## Overview

This model describes a workforce assignment problem. A company has a set of engineers, each with known skills and a home location, and a set of service jobs that require particular skills. The goal is to decide **which engineer should handle each job** while using as little extra training as possible.

A useful way to read it is:

- each job needs one engineer,
- engineers may already have the needed skill,
- if not, some engineers are allowed to learn a small number of new skills,
- assignments must still respect workload and travel limits.

This is a **minimization** model: it tries to complete all jobs with the smallest amount of training.

## Main decision variables

The model chooses two kinds of decisions:

- `allocations[i]`: the engineer assigned to job `i`.
- `new_skills[e,t]`: the `t`-th new skill learned by engineer `e`, or `0` if that training slot is unused.

So the model can either match jobs to engineers who already qualify, or pay for training by assigning a missing skill to an engineer.

## Important inputs

The main data items are:

- `sSkills`: the list of all skill names.
- `engineer_skills[e,s]`: whether engineer `e` already has skill `s`.
- `engineer_location[e]`: the engineer's location code/postcode.
- `jobs[i,*]`: information about each job, including at least the required skill.
- `nNewSkillsPerPerson`: how many new skills one engineer may learn.
- `nTrainingCap`: optional cap on total training.
- `nMaxJobs` and `nMinJobs`: optional upper and lower bounds on jobs per engineer.
- `nInterstateCap` and `nOverseasCap`: optional travel-related limits.
- `allEng`: if `true`, the usual skill-matching rule is turned off.

## Core constraints

The model enforces the following ideas:

1. **Every job gets one engineer.**
2. **Skill compatibility:** if `allEng = false`, an engineer can take a job only if they already have the required skill or are given that skill through `new_skills`.
3. **Training is limited:** each engineer has only a fixed number of training slots, and there may also be a global training cap.
4. **Workload is limited:** engineers can be forced to handle at least `nMinJobs` and at most `nMaxJobs` jobs.
5. **Travel is limited:** overseas and interstate jobs per engineer can be capped.

## Objective

The objective variable is

- `objective =` the total number of nonzero entries in `new_skills`.

So the solver minimizes the **number of training decisions**. Intuitively, the model prefers to reuse existing skills whenever possible and only introduces training when needed to make the assignment feasible or better.

## Output

The model prints:

- the job-to-engineer assignment array `allocations`,
- the learned skills array `new_skills`,
- the final objective value.

## Uncertainty and interpretation notes

Some parts of the data format are not fully documented inside the model. In particular, the model clearly uses:

- `jobs[i,1]` as the required skill,
- `jobs[i,4]` in the interstate test,
- `jobs[i,5]` in the overseas test.

From the code, it is reasonable to infer that column 4 encodes a job location/postcode and column 5 is an overseas flag, but that interpretation is **inferred from usage**, not explicitly explained in comments.

Also, the model minimizes only training count. It does **not** directly optimize fairness, distance, travel cost, or job priority unless those effects are indirectly forced by the constraints.

## References

Identifiable repository references:

- benchmark name: `skill-allocation`
- MiniZinc Challenge instances listed in metadata for **2020** and **2025**
- model file: `skill_allocation_only.mzn`

No explicit paper, authorship, or external problem-source citation is embedded in the model or local metadata, so a stronger bibliographic reference cannot be confirmed from the available files.
