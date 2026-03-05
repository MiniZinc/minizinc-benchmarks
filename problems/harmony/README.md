# Harmony Generation Model

## Overview

This MiniZinc model generates a four-part harmony for a given melody following classical music theory rules. It assigns pitches to four voices (Soprano, Alto, Tenor, Bass) and selects chords for each time step to harmonise the melody. The model enforces voice-leading constraints, chord structure rules, and cadence requirements to produce musically coherent progressions.

---

## Problem Description

The task is to harmonise a melody by:

- Assigning pitches to four voices within their respective ranges.
- Choosing chords that fit the melody and follow harmonic conventions.
- Ensuring smooth voice leading and avoiding forbidden intervals.

The model supports enforcing cadences and controlling musical features such as voice movement and chord progression patterns.

---

## Key Components

### Inputs

- **melody**: Array of MIDI pitches representing the soprano line.
- **key**: The home key (tonic note).
- **maxTime**: Number of chords/time steps (equal to melody length).
- **Voice ranges**:
  - Soprano: C4–G5
  - Alto: G3–C5
  - Tenor: C3–G4
  - Bass: F2–C4
- **Chord types**: `{ I, ii, iii, IV, V, V7, vi }`
- **Cadence types**: Perfect, Plagal, Imperfect, Interrupted.
- **Parameters**:
  - `enforce_cadences`: Boolean to enforce cadence rules.
  - Minimum counts for each cadence type.
  - `max_stationary`: Maximum allowed consecutive stationary notes for inner voices.

---

### Decision Variables

- `music[Voice, Time]`: Pitch assigned to each voice at each time step.
- `chords[Time]`: Chord chosen for each time step.
- `objective`: A measure combining:
  - Sum of largest jumps in each voice.
  - Number of non-root position chords.
  - Number of chords where the root is not doubled.

---

## Constraints

1. **Voice Ranges**: Each voice stays within its defined pitch range.
2. **Voice Crossing**: Voices maintain strict descending order (Soprano > Alto > Tenor > Bass).
3. **Chord Membership**: Notes played match the chosen chord.
4. **Spacing**: Soprano-Alto and Alto-Tenor intervals ≤ one octave.
5. **Forbidden Intervals**:
   - No consecutive perfect fifths.
   - No consecutive octaves.
6. **Cadences**:
   - Every 4th chord pair forms a cadence.
   - Final cadence is perfect or plagal.
   - Minimum counts for cadence types enforced.
7. **Voice Movement**:
   - Voices cannot remain stationary for too long.
   - Each phrase (8 chords) must have sufficient pitch variation.
8. **Chord Progression**:
   - Chords change at every time step.
   - No immediate repetition of 4-chord progressions.
9. **Leading Note Resolution**: Leading tone moves to tonic when cadences are enforced.

---

## Objective

Minimise:
\[
\text{objective} = \text{sum of max jumps} + \text{non-root chords} + \text{non-doubled root chords}
\]
This encourages smooth voice leading and proper chord structure.

---

## Output

- Objective value.
- Lowest note used.
- Visual representation of voice assignments across the pitch range.

---

### Notes

- This model applies classical harmony rules and can be adapted for different styles by modifying constraints.
- Useful for algorithmic composition, music education, and automated harmonisation tasks.

---
