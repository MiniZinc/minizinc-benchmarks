include "globals.mzn";

% MIDI notes
enum Pitch = Pitch(0..127);
% Musical notes
enum Note = {C, 'C#', Db, D, E, 'D#', Eb, F, 'F#', Gb, G, 'G#', Ab, A, 'A#', Bb, B};

% Convert note and octave into MIDI pitch
function Pitch: note(Note: note, int: octave) = let {
  any: notes = [(C, 0), ('C#', 1), (Db, 1), (D, 2), ('D#', 3), (Eb, 3), (E, 4), (F, 5), ('F#', 6), (Gb, 6), (G, 7), ('G#', 8), (Ab, 8), (A, 9), ('A#', 10), (Bb, 10), (B, 11)];
  any: offset = min (n in notes where n.1 = note) (n.2);
  any: start = (octave + 1) * 12
} in Pitch(start + offset);

% Chords
enum Chord = { I, ii, iii, IV, V, V7, vi };
% Pitches of notes in chords relative to home key
array [Chord] of set of int: chord_pitches = [
  I: {0, 4, 7},
  ii: {2, 5, 9},
  iii: {4, 7, 11},
  IV: {5, 9, 12},
  V: {7, 11, 14},
  V7: {7, 11, 14, 17},
  vi: {9, 12, 16},
];
array [Chord] of set of int: chord_offsets = [c: {(v + Pitch^-1(note(key, 4))) mod 12 | v in chord_pitches[c]} | c in Chord];

% Cadences
any: perfect_cadences = [(V, I), (V7, I)];
any: plagal_cadences = [(IV, I)];
any: imperfect_cadences = [(I, V), (ii, V), (IV, V), (vi, V)];
any: interrupted_cadences = [(V, vi), (V7, vi)];
any: all_cadences = perfect_cadences ++ plagal_cadences ++ imperfect_cadences ++ interrupted_cadences;

bool: enforce_cadences;
int: min_perfect;
int: min_plagal;
int: min_imperfect;
int: min_interrupted;

int: max_stationary;

% Voices
enum Voice = { Soprano, Alto, Tenor, Bass };
array [Voice] of set of Pitch: range = [
  Soprano: note(C, 4)..note(G, 5),
  Alto: note(G, 3)..note(C, 5),
  Tenor: note(C, 3)..note(G, 4),
  Bass: note(F, 2)..note(C, 4)
];
set of Pitch: used_range = let {
  any: u = array_union(range);
} in min(u)..max(u);
set of Voice: otherVoices = Voice diff {Soprano};

% Number of chords to harmonise
int: maxTime = length(melody);
enum Time = Time(index_set(melody));

% Home key
Note: key;

array [int] of Pitch: melody;

% constraint trace("\(melody)\n");

% The notes to play
array [Voice, Time] of var Pitch: music;
array [Time] of var Chord: chords;

constraint music[Soprano, ..] = array1d(Time, melody);

any: note_numbers = [(v, t): Pitch^-1(music[v, t]) mod 12 | v in Voice, t in Time];

% The notes played must be within range
constraint forall (v in Voice, t in Time) (music[v, t] in range[v]);

% The voices must not cross/overlap
constraint forall (t in Time) (strictly_decreasing(music[.., t]));

% The notes played must be the notes of the chosen chord
any: chord_notes = [{ note_numbers[v, t] | v in Voice } | t in Time];
constraint forall (t in Time) (chord_notes[t] = chord_offsets[chords[t]]);

% Soprano-alto and Alto-Tenor must be <= 8ve apart
constraint forall (t in Time) (Pitch^-1(music[Soprano, t]) - Pitch^-1(music[Alto, t]) <= 13);
constraint forall (t in Time) (Pitch^-1(music[Alto, t]) - Pitch^-1(music[Tenor, t]) <= 13);

function var int: interval(Voice: v, Voice: u, var Time: t) = abs(music[v, t] - music[u, t]) mod 12;

% No consecutive 5ths
constraint forall (t in Time where t < max(Time)) (
  forall (v, u in Voice where v < u) (
    (interval(v, u, t) == 7) -> (interval(v, u, enum_next(t)) != 7)
  )
);

% No consecutive 8ves
constraint forall (t in Time where t < max(Time)) (
  forall (v, u in Voice where v < u) (
    (interval(v, u, t) == 0) -> (interval(v, u, enum_next(t)) != 0)
  )
);

% Largest jump by each voice
any: max_jump = [v: max (t in Time where t < max(Time)) (abs(music[v, t] - music[v, enum_next(t)])) | v in Voice];

% Range used by each voice
any: range_used = [v: max(music[v, ..]) - min(music[v, ..]) + 1 | v in Voice];

% Number of non-root position chords
var int: non_root :: output = count (t in Time) (note_numbers[Bass, t] != min(chord_notes[t]));

% Number of chords with a note other than the root doubled
var int: non_doubled_root :: output = count (t in Time) (count (v in Voice) (note_numbers[v, t] == min(chord_notes[t])) == 1);

% Chords must change each time step
constraint forall (t in Time where t < max(Time)) (chords[t] != chords[enum_next(t)]);

% End of every 4 chords is a cadence
any: cadences :: output = [(chords[Time(t)], chords[Time(t + 1)]) | t in 1..maxTime where t mod 4 = 3];
constraint enforce_cadences -> forall (c in cadences) (c in all_cadences);

% Leading note goes to tonic
constraint enforce_cadences -> forall (v in Voice, t in Time where Time^-1(t) mod 2 = 1 /\ t < max(Time)) (note_numbers[v, t] = (Pitch^-1(note(key, 0)) + 11) mod 12 -> music[v, enum_next(t)] = enum_next(music[v, t]));

% Final cadence is perfect or plagal
constraint enforce_cadences -> cadences[max(index_set(cadences))] in [(V, I), (IV, I)];

% Enforce minimum counts of cadence types
constraint count (c in cadences) (c in perfect_cadences) >= min_perfect;
constraint count (c in cadences) (c in plagal_cadences) >= min_plagal;
constraint count (c in cadences) (c in imperfect_cadences) >= min_imperfect;
constraint count (c in cadences) (c in interrupted_cadences) >= min_interrupted;

% 4 chord progression doesn't immediately repeat
constraint forall (t in 2..maxTime div 4) (array1d(chords[Time((t - 2) * 4 + 1..(t - 1) * 4)]) != array1d(chords[Time((t - 1) * 4 + 1..t * 4)]));

% Voice doesn't stay stationary for too long
constraint forall (v in otherVoices, t in 1..maxTime - max_stationary) (not all_equal(music[v, Time(t..t + max_stationary)]));

% Phrases have some movement
constraint forall (v in otherVoices, t in 1..maxTime where t mod 8 = 1) (max (u in t..t + 7) (music[v, Time(u)]) - min (u in t..t + 7) (music[v, Time(u)]) > 4);

% Objective
var int: objective :: output = sum(max_jump) + non_root + non_doubled_root;

enum SearchVar = { ChordVar } ++ VoiceVar(Voice);
solve :: int_search(
  [
    if x = ChordVar then
      let { var int: v = chords[t]; } in v
    else
      let { var int: v = music[VoiceVar^-1(x), t]; } in v
    endif
  |
    t in Time,
    x in SearchVar
  ],
  input_order,
  indomain_min
) minimize objective;

output "objective: \(objective)\n";
output "lowest note: \(Pitch^-1(min(fix(music))))\n";
output join("\n", [concat(p in used_range) (
  if p = fix(music[Soprano, t]) then "S"
  elseif p = fix(music[Alto, t]) then "A"
  elseif p = fix(music[Tenor, t]) then "T"
  elseif p = fix(music[Bass, t]) then "B"
    else " " endif
) | t in Time]) ++ "\n";
