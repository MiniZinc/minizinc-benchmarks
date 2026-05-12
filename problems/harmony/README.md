# Four-Voice Harmony

## Problem Description

This model solves the **four-part harmonization** problem from classical music theory. Given a fixed soprano melody (a sequence of musical notes), the task is to assign pitches to three additional voices — **Alto**, **Tenor**, and **Bass** — and to choose a **chord** for each time step, such that the resulting four-voice arrangement follows the traditional rules of Western tonal harmony.

The goal is to produce a harmonically correct and musically pleasing accompaniment, much like the four-part chorales written by J.S. Bach. This type of problem has been well-studied in the music AI and constraint programming literature as a benchmark for rule-based music generation.

## Input Parameters

| Parameter                                                       | Description                                                                              |
| --------------------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| `melody`                                                        | The soprano melody as a sequence of MIDI pitches (fixed, not a decision variable)        |
| `key`                                                           | The home key of the piece (e.g., C major), which determines which chords are available   |
| `enforce_cadences`                                              | Whether cadence rules at phrase boundaries are enforced                                  |
| `min_perfect`, `min_plagal`, `min_imperfect`, `min_interrupted` | Minimum required counts of each cadence type across the piece                            |
| `max_stationary`                                                | The maximum number of consecutive time steps a non-soprano voice may hold the same pitch |

The five included instances correspond to well-known melodies: _Twinkle Twinkle Little Star_, a _Canon_, a _Minuet_, _Ode to Joy_, and _Frère Jacques_ (_Brother John_).

## Decision Variables

| Variable             | Description                                                                                                                                                       |
| -------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `music[Voice, Time]` | The MIDI pitch played by each voice at each time step. The Soprano row is fixed by the input melody; the Alto, Tenor, and Bass rows are determined by the solver. |
| `chords[Time]`       | The chord chosen for each time step, drawn from the seven diatonic chords of the home key: I, ii, iii, IV, V, V7, vi.                                             |

## Constraints

The constraints encode the classical rules of four-part writing:

- **Correct chord tones**: At each time step, every voice must play a note that belongs to the chosen chord.
- **Voice ranges**: Each voice is restricted to its traditional range (e.g., Soprano: C4–G5, Bass: F2–C4).
- **No voice crossing**: Voices must be strictly ordered from highest (Soprano) to lowest (Bass) at every time step — they must not cross over one another.
- **Spacing**: The interval between adjacent upper voices (Soprano–Alto and Alto–Tenor) must not exceed one octave.
- **No consecutive perfect fifths**: Two voices must not move in parallel to a perfect fifth (a well-known rule of counterpoint).
- **No consecutive octaves**: Two voices must not move in parallel to an octave (or unison).
- **Chord variety**: Chords must change at every time step; a four-chord phrase must not immediately repeat.
- **Cadences**: At the end of every four-chord phrase, the chord progression must form a recognized cadence (perfect, plagal, imperfect, or interrupted). The final cadence must be a perfect or plagal cadence. Minimum counts for each cadence type are also enforced.
- **Leading-note resolution**: On odd beats, if a voice is playing the leading note (the seventh degree of the scale), it must rise to the tonic on the next beat.
- **Voice movement**: No non-soprano voice may remain stationary for more than `max_stationary` consecutive steps. Each voice must also span a meaningful range within every eight-step phrase.

## Objective

The model **minimizes** a weighted combination of three penalty terms:

1. **Total melodic movement** (`sum(max_jump)`): The sum of the largest single-step interval leap made by each voice. Smaller jumps are preferred as they produce smoother voice leading.
2. **Non-root-position chords** (`non_root`): The number of time steps where the Bass is not playing the root (lowest note) of the chord. Root position is generally preferred in traditional harmony.
3. **Non-doubled-root chords** (`non_doubled_root`): The number of time steps where the root of the chord is not present in at least two voices. Doubling the root gives a chord a fuller, more stable sound.

## Notes

The model uses MIDI note numbering (0–127) for pitch representation. The `note` function converts a symbolic note name and octave into a MIDI pitch number, and all interval calculations are performed modulo 12 to account for octave equivalence. The available chords and their constituent intervals are hard-coded relative to the home key, so the model implicitly assumes **major mode** throughout.

## References

Four-part harmonization is a classic problem in music AI. Relevant background can be found in:

- Ozgur, A. et al. (2020). _Constraint-based Music Harmonization_. Various constraint programming workshops and proceedings have addressed this problem over many years.
- Tsang, E., & Marsden, A. (1997). _Harmony in Constraint Satisfaction_. Proceedings of the IJCAI Workshop on Music and AI.

> **Note for experts**: The exact provenance of this specific model is uncertain. If you recognise it as originating from a particular paper or competition, please update this reference section.

## Model update summary

Added concise inline comments in harmony.mzn to clarify:

- melody/chord decision variable roles,
- objective composition across voicing penalties,
- optimization intent for smooth and stable harmonization.
