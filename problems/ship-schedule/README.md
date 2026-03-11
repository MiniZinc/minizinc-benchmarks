# Ship Scheduling

## Problem Description

A port needs to schedule a fleet of ships to depart (and some to arrive) within a planning horizon divided into discrete **time slots**. The central challenge is that ships are large vessels that must navigate a shallow channel, so the depth of water — the _draft_ — available to each ship at any given time slot is constrained by tidal and wave conditions. A ship loaded with more cargo sits deeper in the water; if the tide is too low, the ship must either wait for a better slot or carry less cargo. This model chooses _when_ each ship sails to maximise the total amount of cargo that departs.

Beyond tides, the real port environment introduces further complications:

- Some ships may still be loading and cannot sail before a certain earliest time.
- Ships share a narrow channel, so pairs of ships must maintain a minimum **separation time** to avoid collision risk.
- Incoming ships may need the same **berth** as an outgoing ship; the outgoing ship must leave before the incoming one can dock.
- A limited pool of **tugboats** assists ships through the channel; the schedule must never demand more tugs simultaneously than are available.

## Decision Variables

| Variable                  | Meaning                                                                                               |
| ------------------------- | ----------------------------------------------------------------------------------------------------- |
| `TransitStartTimeSlot[s]` | The time slot at which ship _s_ begins its transit                                                    |
| `ShipSails[s]`            | 1 if ship _s_ is scheduled to sail, 0 otherwise                                                       |
| `Draft_cm[s]`             | The sailing draft (in cm) awarded to ship _s_, determined by tidal conditions at its chosen time slot |
| `TugsBusy[s, t, k]`       | Number of tugs from set _k_ occupied by ship _s_ during time slot _t_                                 |
| `TugsBusyExtra[s]`        | Extra tugs reserved for ship _s_ when it closely follows an incoming ship                             |

## Objective

**Maximise total cargo loaded across all sailing ships:**

$$\text{maximise} \sum_{s=1}^{N_\text{Ships}} \text{ShipSails}[s] \times \text{Draft\_cm}[s] \times \text{TonnesPerCmDraft}[s]$$

Each additional centimetre of allowed draft lets a ship carry more tonnes of cargo. Larger ships (higher `TonnesPerCmDraft`) gain more from a favourable time slot, so the solver must balance the needs of differently-sized vessels within the tidal window.

## Key Constraints

1. **Draft assignment** — A ship's draft is exactly the maximum allowable draft at its chosen time slot; a slot with draft 0 forces `ShipSails = 0`.
2. **Earliest sailing time** — A sailing ship cannot depart before it has finished loading.
3. **Berth swap** — An outgoing ship must start its transit within a bounded time difference relative to the incoming ship that needs its berth.
4. **Separation time** — Any two sailing ships must be separated by at least `MinSeparationTimeSlots` in either order.
5. **Tug availability** — The total tugs occupied by incoming ships at any time slot, and separately by outgoing ships (including an extra allowance when an outbound immediately follows an inbound), must not exceed `NTugs`.

## Data and Uncertainty

The tidal and wave conditions are pre-processed into the `MaxSailingDraft_cm` array before the solver runs. This means the model optimises over a _forecast_ of sea conditions rather than exact future values. In practice the quality of the schedule depends on the accuracy of those tide and weather predictions, which introduces real-world uncertainty not captured inside the model itself.

## Instances

Instances from the MiniZinc Challenges range from 3 to 8 ships (e.g., `4Ships`, `6ShipsMixed`, `8ShipsUnconst`). The "Mixed" label indicates schedules containing both incoming and outgoing ships; "Unconst" suggests fewer binding tug or separation constraints.

## References

- Model authored by **Elena Kelareva** (2011).
- Featured in the **MiniZinc Challenge** competitions in 2011, 2012, and 2014.
- MiniZinc Challenge: <https://www.minizinc.org/challenge.html>
