# Unit Commitment (Beginner-Friendly Explanation)

This MiniZinc model describes a **unit commitment** problem: deciding which power generators should be ON or OFF over time, how much each ON generator should produce, and whether any demand must be unmet (load shedding), while minimizing total operating cost.

In simple terms, the model asks:
- Which generators run in each time period?
- How much power should each running generator produce?
- Can generation changes happen fast enough (ramping limits)?
- If demand cannot be fully met, how much load is shed, and what penalty is paid?

---

## 1) Problem setup

The model works over:
- A set of time periods (`TIME`)
- A set of generators (`GEN`)
- A set of loads (`LOAD`)

Input data includes:
- Generator max/min output (`gen_max`, `gen_min`)
- Initial ON/OFF status (`init_commitment`)
- Demand per load and time (`demand`)
- Costs: generation, startup, shutdown, and load shedding penalties
- Operational limits: ramp rate, minimum downtime, maximum number of starts

It uses a simplified **single-bus (copper-plate)** network assumption, meaning all generation and demand are pooled with no transmission constraints.

---

## 2) Decision variables

The optimization chooses:
- `commitment[g,t]` (boolean): whether generator `g` is ON at time `t`
- `generation[g,t]` (integer): produced power by generator `g` at time `t`
- `loss_of_load[l,t]` (integer): unmet demand for load `l` at time `t`
- `up[g,t]` / `down[g,t]` (boolean): startup/shutdown indicators between consecutive periods

These variables are linked so that generation is only possible when committed, and startup/shutdown events match changes in commitment.

---

## 3) Main constraints (what makes a schedule feasible)

1. **Generator output limits**
   - If a unit is OFF, generation must be 0.
   - If ON, generation must stay between minimum and maximum output.

2. **Load shedding bound**
   - Shedding at each load/time cannot exceed that load’s demand.

3. **Initial condition**
   - Commitment at time 1 is fixed to the given initial status.

4. **Startup/shutdown logic**
   - `up[g,t]` is true when a generator goes OFF→ON.
   - `down[g,t]` is true when a generator goes ON→OFF.

5. **Power balance (single-bus)**
   - Total generation equals total served demand:
     - served demand = demand − shed load

6. **Ramping constraints**
   - For periods without startup/shutdown transitions, generator output changes are limited by each unit’s ramp rate.

7. **Minimum downtime**
   - After shutdown, a unit must remain OFF for at least `min_down[g]` periods.

8. **Maximum number of starts**
   - Number of startups per generator is capped by `max_num_start[g]`.

---

## 4) Objective (what is minimized)

The model minimizes total cost:

- Dispatch cost: generation amount × marginal production cost
- Startup cost: paid when `up[g,t] = true`
- Shutdown cost: paid when `down[g,t] = true`
- Load shedding penalty: unmet demand × shedding cost

So the solver trades off economic operation, switching costs, and reliability (avoiding expensive unmet demand).

---

## 5) Uncertainty and modeling assumptions

Based on this model file alone, several practical details are simplified or uncertain:
- **Network physics not modeled** beyond one-bus balance (no line limits, losses, or congestion).
- **Reserve/security constraints** are not explicit (e.g., spinning reserve, N-1 reliability).
- **Unit dynamics** such as minimum up-time, startup trajectories, or nonlinear efficiency are simplified.
- **Data semantics** (units, timescale, cost calibration) depend on external datasets not shown here.
- **Ramping treatment during transitions** is conditional on startup/shutdown flags; this may differ from other UC formulations.

These are normal simplifications for benchmark optimization models but should be checked before real-world operational use.

---

## 6) Potential references identifiable from the model

The model comments suggest links to common UC literature and policy context:
- **Unit Commitment (UC)** in power systems operations research.
- **Copper-plate / single-bus approximation** used in simplified power-flow formulations.
- A comment mentions a startup cap related to **U.S. DoE emission** considerations.

No explicit paper citation, report title, DOI, or URL is included in the model file, so exact bibliographic references cannot be confirmed from this source alone.
