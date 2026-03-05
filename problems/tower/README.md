# Tower Power Allocation

This directory contains a MiniZinc model (`tower.mzn`) that decides how much
power each cellular tower should emit, and which tower each handset connects to,
subject to capacity and signal strength requirements.  The goal is to maximise
service quality given physical and budgetary constraints.

## Inputs

- `TOWER` and `HANDSET` are enumerations of available towers and mobile
  devices.
- `capacity[t]` is the number of handsets that tower `t` can serve without
  becoming overloaded.
- `demand[h]` is the bandwidth (or load) required by handset `h`.
- `min_signal_strength` is the minimal acceptable signal level for a handset to
  connect.
- Power levels are discretised: `POWER = 1..maxpower` and
  `effective_power[p] = 2*(p-1)^2` models the emitted power at level `p`.
- `distance[h,t]` gives the (real) distance between handset `h` and tower `t`.
- `attenuation` and `attenuation_i` precompute signal loss between handsets and
  towers; the latter rounds to integers for the solver.
- `POWER_SCALE` is a scaling constant used to keep computations integral.

## Decision variables

- `power[t]` chooses an integer power level for each tower.
- `tower[h]` assigns handset `h` to the tower that provides the strongest signal.
- `connection_quality[h]` is a derived integer representing whether the chosen
  tower is overloaded (0) or not (1); the model maximises the sum over all
  handsets.

## Constraints

1. Each handset must receive at least `min_signal_strength` from its assigned
   tower.  The helper function `min_transmit_power` computes the smallest power
   level that achieves this, and a constraint forces `power[t]` to be at least
   that value whenever handset `h` is connected to tower `t`.
2. Overloaded towers (more demand than capacity) are tracked via a
   `global_cardinality_low_up` constraint; overloaded towers decrease the
   `connection_quality` of devices served by them.
3. A handset is always assigned to the tower with the maximal signal
   strength; this is encoded using a custom `arg_max` function.

## Objective

Maximise total `connection_quality`, which effectively attempts to serve as many
handsets as possible without exceeding tower capacities and while maintaining
minimum signal levels.
