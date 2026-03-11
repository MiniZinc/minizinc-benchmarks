%% Integrated Healthcare Timetabling

/*
This model was developed to compete in the Integrated Healthcare Timetabling Competition 2024
(https://ihtc2024.github.io/).

All constraint descriptions (see comments marked with H<n> and S<n> throughout the model)
were copied from the competition's problem specification.

This model is released under the terms of the MIT license (see LICENSE.txt).

Contact: Michael Marte <informarte@freenet.de>
*/

% Modifications by MiniZinc Challenge Organizers:
% - Modify search annotation to allow running in FD

include "all_different.mzn";
include "bin_packing_load.mzn";
include "cumulative.mzn";
include "nvalue_fn.mzn";


%% Input

int: days;
int: skill_levels;
array[1..3] of string: shift_types;
list of string: age_groups;
list of string: genders;

type Occupant = record(
  string: id,
  int: index,
  string: gender,
  string: age_group,
  int: length_of_stay,
  list of int: workload_produced,
  list of int: skill_level_required,
  string: room_id  
);

list of Occupant: occupants;

type Patient = record(
  string: id,
  int: index,
  string: gender,
  string: age_group,
  int: length_of_stay,
  int: surgery_release_day,
  % Only mandatory patients have a valid due date.
  int: surgery_due_day,
  int: surgery_duration,
  list of int: workload_produced,
  list of int: skill_level_required,
  bool: mandatory,
  string: surgeon_id,
  list of string: incompatible_room_ids
);

list of Patient: patients;

type Surgeon = record(
  string: id,
  int: index,
  list of int: max_surgery_time
);

list of Surgeon: surgeons;

type OperatingTheater = record(
  string: id,
  int: index,
  list of int: availability
);

list of OperatingTheater: operating_theaters;

type Room = record(
  string: id,
  int: index,
  int: capacity
);

list of Room: rooms;

type WorkingShift = record(
  int: day,
  string: shift,
  int: max_load
);

type Nurse = record(
  string: id,
  int: index,
  int: skill_level,
  list of WorkingShift: working_shifts
);

list of Nurse: nurses;

type Weights = record(
  int: room_mixed_age,
  int: room_nurse_skill,
  int: continuity_of_care,
  int: nurse_eccessive_workload,
  int: open_operating_theater,
  int: surgeon_transfer,
  int: patient_delay,
  int: unscheduled_optional
);

Weights: weights;


%% Index sets

/*
DAYS is the scheduling period.
All mandatory patients have to be admitted on days in DAYS, see H5.
The extended scheduling period XDAYS is used for optional patients:
If an optional patient is admitted on a day in XDAYS \ DAYS,
then the patient is considered as "unscheduled".
XXDAYS is the period during which resource consumption may occur
due to admitting patients in XDAYS. (There are no constraints on
the roster outside DAYS.)
*/

set of int: DAYS = 1..days;
set of int: XDAYS = 1..(days + max(1, days div 3));
set of int: XXDAYS = 1..(max([occupant.length_of_stay | occupant in occupants] ++
                             [max(XDAYS) + patient.length_of_stay - 1 | patient in patients]));
set of int: SHIFTS = 1..length(shift_types);
set of int: AGE_GROUPS = 1..length(age_groups);
set of int: GENDERS = 1..length(genders);
set of int: PATIENTS = 1..length(patients);
set of int: OCCUPANTS = 1..length(occupants);
set of int: ROOMS = 1..length(rooms);
set of int: SURGEONS = 1..length(surgeons);
set of int: OPERATING_THEATERS = 1..length(operating_theaters);
set of int: NURSES = 1..length(nurses);
set of int: SKILL_LEVELS = 0..(skill_levels - 1);


%% Decision variables

array[PATIENTS] of var XDAYS: admission_days;

array[PATIENTS] of var ROOMS: room_assignments;

array[PATIENTS] of var OPERATING_THEATERS: ot_assignments;

int: NO_NURSE_ASSIGNMENT = min(NURSES) - 1;
array[ROOMS, XXDAYS, SHIFTS] of var NO_NURSE_ASSIGNMENT..max(NURSES): nurse_assignments;

constraint forall(r in ROOMS, d in XXDAYS, s in SHIFTS)(
  if d in DAYS
  then nurse_assignments[r, d, s] != NO_NURSE_ASSIGNMENT
  else nurse_assignments[r, d, s] = NO_NURSE_ASSIGNMENT
  endif
);


%% Helper functions and predicates

function Room: room(Occupant: occupant) =
  [room | room in rooms where occupant.room_id == room.id][1];

function Surgeon: surgeon(Patient: patient) =
  [surgeon | surgeon in surgeons where patient.surgeon_id == surgeon.id][1];

function bool: nurse_is_scheduled(Nurse: nurse, DAYS: d, SHIFTS: s) =
  length(
    [working_shift |
     working_shift in nurse.working_shifts
     where working_shift.day == d /\ working_shift.shift == shift_types[s]]
  ) == 1;

function int: nurse_capacity(Nurse: nurse, DAYS: d, SHIFTS: s) =
  [working_shift.max_load |
   working_shift in nurse.working_shifts
   where working_shift.day == d /\ working_shift.shift == shift_types[s]][1];

array[NURSES] of int: max_nurse_capacities =
  [max([nurse_capacity(nurse, d, s) | d in DAYS, s in SHIFTS where nurse_is_scheduled(nurse, d, s)]) | nurse in nurses];

function bool: nurse_is_scheduled_with_reduced_capacity(NURSES: n, DAYS: d, SHIFTS: s) =
  nurse_is_scheduled(nurses[n], d, s) /\ nurse_capacity(nurses[n], d, s) < max_nurse_capacities[n];

function bool: patient_can_have_surgery_on_day(Patient: patient, DAYS: d) =
  patient.surgery_release_day <= d /\
  (not patient.mandatory \/ d <= patient.surgery_due_day);

function bool: patient_can_be_in_hospital_on_day(Patient: patient, DAYS: d) =
  patient.surgery_release_day <= d /\
  (not patient.mandatory \/ d <= patient.surgery_due_day + patient.length_of_stay - 1);

function bool: patient_can_be_in_room_on_day(Patient: patient, Room: room, DAYS: d) =
    patient_can_be_in_hospital_on_day(patient, d) /\
    length([id | id in patient.incompatible_room_ids where room.id == id]) == 0;

int: total_length_of_stays =
  sum(occupant in occupants)(occupant.length_of_stay) +
  sum(patient in patients)(patient.length_of_stay);

% Shortcut for a conjunction of cumulative constraints where the assignment of tasks
% to machines is subject to optimization.
predicate cumulatives(
  array[$$E] of var int: s,
  array[$$E] of var int: d,
  array[$$E] of var int: r,
  array[$$E] of var $$M: m,
  array[$$M] of var int: b)
=
  forall(i in index_set(b))(
    let {set of int: J = {j | j in index_set(s) where i in dom(m[j])}}
    in cumulative(
      [s[j] | j in J],
      [d[j] | j in J],
      [if m[j] == i then r[j] else 0 endif | j in J],
      b[i])
  );


%% H5 Mandatory versus optional patients: All mandatory patients must be ad-
%% mitted within the scheduling period, whereas optional patients may be post-
%% poned to future scheduling periods.
%% H6 Admission day: A patient can be admitted on any day from their release
%% date to their due date. Given that optional patients do not have a due date,
%% they can be admitted on any day after their release date.

constraint forall(p in PATIENTS)(admission_days[p] >= patients[p].surgery_release_day);
constraint forall(p in PATIENTS where patients[p].mandatory)(
  admission_days[p] in DAYS /\ admission_days[p] <= patients[p].surgery_due_day
);


%% H1 No gender mix: Patients of different genders may not share a room on any day.

% The counts cannot be greater than card(OCCUPANTS) + card(PATIENTS)
% but according, redundant domains would be costly to check.
array[ROOMS, XXDAYS, GENDERS] of var 0..total_length_of_stays: gender_counts;

constraint forall(g in GENDERS, gender = genders[g])(
  let {
    list of Occupant: occupant_subset =
      [occupant | occupant in occupants where occupant.gender == gender],
    list of Patient: patient_subset =
      [patient | patient in patients where patient.gender == gender]
  }
  in bin_packing_load(
    [gender_counts[r, d, g] | r in ROOMS, d in XXDAYS],
    [(room(occupant).index - 1) * card(XXDAYS) + i |
     occupant in occupant_subset,
     i in 1..occupant.length_of_stay] ++
    [(room_assignments[p] - 1) * card(XXDAYS) + (admission_days[p] - 1) + i |
     patient in patient_subset,
     p = patient.index,
     i in 1..patient.length_of_stay],
    [1 | occupant in occupant_subset, i in 1..occupant.length_of_stay] ++
    [1 | patient in patient_subset, i in 1..patient.length_of_stay]
  )
);

constraint forall(r in ROOMS, d in DAYS)(
  sum(g in GENDERS)(gender_counts[r, d, g] > 0) <= 1
);


%% H2 Compatible rooms: Patients can only be assigned to one of their compatible rooms.

constraint forall(p in PATIENTS, room_id in patients[p].incompatible_room_ids, r in ROOMS where rooms[r].id == room_id)(
  room_assignments[p] != r
);


%% H3 Surgeon overtime: The maximum daily surgery time of a surgeon must not be exceeded.

% Sanity check
constraint forall(surgeon in surgeons)(
  sum(patient in patients where patient.mandatory /\ patient.surgeon_id == surgeon.id)(patient.surgery_duration) <=
  sum(surgeon.max_surgery_time)
);

% Redundant constraint:
% Deny admission on days where the surgeon is absent or does not have enough capacity.
constraint forall(p in PATIENTS, patient = patients[p])(
  admission_days[p] in
    ({d | d in DAYS where surgeon(patient).max_surgery_time[d] >= patient.surgery_duration}
    union (XDAYS diff DAYS))
);

% Main constraint
constraint forall(surgeon in surgeons)(
  let {
    list of Patient: patient_subset =
      [patient | patient in patients where patient.surgeon_id == surgeon.id],
    int: max_demand = sum(patient in patient_subset)(patient.surgery_duration)
  }
  in cumulative(
    [admission_days[patient.index] | patient in patient_subset] ++
    [d | d in DAYS where surgeon.max_surgery_time[d] < max_demand],
    [1 | patient in patient_subset] ++
    [1 | d in DAYS where surgeon.max_surgery_time[d] < max_demand],
    [patient.surgery_duration | patient in patient_subset] ++
    [max_demand - surgeon.max_surgery_time[d] |
     d in DAYS
     where surgeon.max_surgery_time[d] < max_demand],
    max_demand
  )
);


%% H4 OT overtime: The duration of all surgeries allocated to an OT on a day
%% must not exceed its maximum capacity.

% Sanity check
constraint
  sum(patient in patients where patient.mandatory)(patient.surgery_duration) <=
  sum(operating_theater in operating_theaters)(sum(operating_theater.availability));

% Redundant constraint:
% Deny admission on days where no suitable OT is available
constraint forall(patient in patients)(
  admission_days[patient.index] in
    {d |
     d in DAYS,
     operating_theater in operating_theaters
     where operating_theater.availability[d] >= patient.surgery_duration}
    union (XDAYS diff DAYS)
);

% Redundant constraint:
% Deny OTs which do not have enough capacity for specific surgeries.
constraint forall(patient in patients)(
  ot_assignments[patient.index] in
    {operating_theater.index |
     operating_theater in operating_theaters
     where exists(d in DAYS)(
       patient_can_have_surgery_on_day(patient, d) /\ operating_theater.availability[d] >= patient.surgery_duration
    )}
);

% Main constraint
constraint let {
    int: max_demand = sum(patient in patients)(patient.surgery_duration)
  }
  in cumulatives(
    admission_days ++ [d | ot in OPERATING_THEATERS, d in DAYS],
    [1 | p in PATIENTS] ++ [1 | ot in OPERATING_THEATERS, d in DAYS],
    [patient.surgery_duration | patient in patients] ++
    [max_demand - operating_theater.availability[d] |
    operating_theater in operating_theaters,
    d in DAYS],
    ot_assignments ++ [ot | ot in OPERATING_THEATERS, d in DAYS],
    [max_demand | operating_theater in operating_theaters],
  );



%% H7 Room capacity: The number of patients in each room in each day cannot
%% exceed the capacity of the room.

constraint let {
    int: max_demand = card(OCCUPANTS) + card(PATIENTS)
  }
  in cumulatives(
    [1 | occupant in occupants] ++ admission_days ++ [1 | room in rooms],
    [occupant.length_of_stay | occupant in occupants] ++
    [patient.length_of_stay | patient in patients] ++
    [card(DAYS) | room in rooms],
    [1 | occupant in occupants] ++ [1 | patient in patients] ++ [max_demand - room.capacity | room in rooms],
    [room(occupant).index | occupant in occupants] ++ room_assignments ++ [room.index | room in rooms],
    [max_demand | room in rooms],
  );


%% Nurse-to-room assignment

constraint forall(d in DAYS, s in SHIFTS)(
  let {set of int: available_nurses = {nurse.index | nurse in nurses where nurse_is_scheduled(nurse, d, s)}}
  in forall(r in ROOMS)(nurse_assignments[r, d, s] in available_nurses)
);


%% S1 Age groups: For each day of the scheduling period and for each room, the
%% maximum difference between age groups of patients sharing the room should
%% be minimized.

% The counts cannot be greater than card(OCCUPANTS) + card(PATIENTS)
% but according, redundant domains would be costly to check.
array[ROOMS, XXDAYS, AGE_GROUPS] of var 0..total_length_of_stays: room_occupations;

constraint forall(a in AGE_GROUPS)(
  let {
    list of Occupant: occupant_subset =
      [occupant | occupant in occupants where occupant.age_group == age_groups[a]],
    list of Patient: patient_subset =
      [patient | patient in patients where patient.age_group == age_groups[a]]
  }
  in bin_packing_load(
    [room_occupations[r, d, a] | r in ROOMS, d in XXDAYS],
    [(room(occupant).index - 1) * card(XXDAYS) + i |
     occupant in occupant_subset,
     i in 1..occupant.length_of_stay] ++
    [(room_assignments[p] - 1) * card(XXDAYS) + (admission_days[p] - 1) + i |
     patient in patient_subset,
     p = patient.index,
     i in 1..patient.length_of_stay],
    [1 | occupant in occupant_subset, i in 1..occupant.length_of_stay] ++
    [1 | patient in patient_subset, i in 1..patient.length_of_stay]
  )
);

array[ROOMS, DAYS, AGE_GROUPS] of var bool: room_has_age_group =
  array3d(
    ROOMS, DAYS, AGE_GROUPS,
    [room_occupations[r, d, a] > 0 | r in ROOMS, d in DAYS, a in AGE_GROUPS]
  );

% This code minimizes the number of if-then-else constraints for frequent cases (n = 3 in particular).
function var int: min_age_group(ROOMS: r, DAYS: d, int: n, var int: fallback) =
  let {int: b = min(AGE_GROUPS)}
  in if n == 1
  then (if room_has_age_group[r, d, b] then b else fallback endif)
  elseif n == 2
  then (if room_has_age_group[r, d, b] then b elseif room_has_age_group[r, d, b + 1] then b + 1 else fallback endif)
  elseif n == 3
  then (if room_has_age_group[r, d, b]then b elseif room_has_age_group[r, d, b + 1] then b + 1 elseif room_has_age_group[r, d, b + 2] then b + 2 else fallback endif)
  else min_age_group(r, d, n - 1, if room_has_age_group[r, d, b + n - 1] then b + n - 1 else fallback endif)
  endif;

% This code minimizes the number of if-then-else constraints for frequent cases (n = 3 in particular).
function var int: max_age_group(ROOMS: r, DAYS: d, int: n, var int: fallback) =
  let {int: b = min(AGE_GROUPS)}
  in if n == 1
  then (if room_has_age_group[r, d, b] then b else fallback endif)
  elseif n == 2
  then (if room_has_age_group[r, d, b + 1] then b + 1 elseif room_has_age_group[r, d, b] then b else fallback endif)
  elseif n == 3
  then (if room_has_age_group[r, d, b + 2] then b + 2 elseif room_has_age_group[r, d, b + 1] then b + 1 elseif room_has_age_group[r, d, b] then b else fallback endif)
  else (if room_has_age_group[r, d, b + n - 1] then b + n - 1 else max_age_group(r, d, n - 1, fallback) endif)
  endif;

var int: total_age_group_differences =
  if card(AGE_GROUPS) == 1
  then 0
  else sum(r in ROOMS, d in DAYS)(
          max(
            0,
            max_age_group(r, d, card(AGE_GROUPS), min(AGE_GROUPS) - 1) -
            min_age_group(r, d, card(AGE_GROUPS), max(AGE_GROUPS) + 1)
          )
       )
  endif;


%% S2 Minimum skill level: The minimum skill level a nurse must have to provide
%% the required care for a patient during each shift of their stay should be met.
%% If the skill level of the nurse assigned to a patient’s room in a shift does
%% not reach the minimum level required by that patient, a penalty is incurred
%% equal to the difference between the two skill levels. Note that a nurse with a
%% skill level greater than the minimum required can be assigned to the room
%% at no additional cost.

% The counts cannot be greater than card(OCCUPANTS) + card(PATIENTS)
% but according, redundant domains would be costly to check.
array[ROOMS, XXDAYS, SHIFTS, 1..max(SKILL_LEVELS)] of var 0..total_length_of_stays: skill_level_requirements;

constraint forall(l in SKILL_LEVELS where l > 0)(
  bin_packing_load(
    [skill_level_requirements[r, d, s, l] | r in ROOMS, d in XXDAYS, s in SHIFTS],
    [(room(occupant).index - 1) * (card(XXDAYS) * card(SHIFTS)) + i |
     occupant in occupants,
     i in index_set(occupant.skill_level_required)
     where occupant.skill_level_required[i] == l] ++
    [(room_assignments[p] - 1) * (card(XXDAYS) * card(SHIFTS)) +
     (admission_days[p] - 1) * card(SHIFTS) +
     i |
     patient in patients,
     p  = patient.index,
     i in index_set(patient.skill_level_required)
     where patient.skill_level_required[i] == l],
    [1 | occupant in occupants, r in occupant.skill_level_required where r == l] ++
    [1 | patient in patients, r in patient.skill_level_required where r == l]
  )
);

% MiniZinc does not support dynamic access to arrays in records.
array [NURSES] of SKILL_LEVELS: nurse_skill_levels = [nurses[n].skill_level | n in NURSES];

var int: total_skill_level_deviation = sum(r in ROOMS, d in DAYS, s in SHIFTS)(
  let {var int: n = nurse_assignments[r, d, s]}
  in sum(l in SKILL_LEVELS where l > 0)(
    max(0, skill_level_requirements[r, d, s, l] * (l - nurse_skill_levels[n]))
  )
);


%% S3 Continuity of care: To ensure continuity of care, the total number of distinct
%% nurses providing care to a patient during their entire stay should be mini-
%% mized. The given rosters assume maximum one shift per day for each nurse,
%% hence the number of different nurses who take care of a patient is at least 3,
%% thus resulting in a minimum cost for this component of 3 times the number
%% of admitted patients.

var int: total_discontinuity_of_care = (
  sum(occupant in occupants)(
    nvalue(
      [NO_NURSE_ASSIGNMENT] ++
      [nurse_assignments[room(occupant).index, min(DAYS) + d - 1, s] |
       d in 1..occupant.length_of_stay,
       s in SHIFTS]
    )
  ) +
  sum(patient in patients, p = patient.index)(
    nvalue(
      [NO_NURSE_ASSIGNMENT] ++
      [nurse_assignments[room_assignments[p], admission_days[p] + i - 1, s] |
       i in 1..patient.length_of_stay,
       s in SHIFTS]
    )
  ) -
  (card(OCCUPANTS) + card(PATIENTS)));


%% S4 Maximum workload: For each shift, the total workload induced by patients
%% staying in rooms assigned to a nurse should not exceed the maximum work
%% load of that nurse in that shift.

set of int: ROOM_WORKLOAD =
  0..(sum([workload | occupant in occupants, workload in occupant.workload_produced]) +
      sum([workload | patient in patients, workload in patient.workload_produced]));
array[ROOMS, XXDAYS, SHIFTS] of var ROOM_WORKLOAD: room_workloads;

constraint bin_packing_load(
  array1d(room_workloads),
  [(room(occupant).index - 1) * (card(XXDAYS) * card(SHIFTS)) + i |
   occupant in occupants,
   i in index_set(occupant.workload_produced)] ++
  [(room_assignments[p] - 1) * (card(XXDAYS) * card(SHIFTS)) + (admission_days[p] - 1) * card(SHIFTS) + i |
   patient in patients,
   p = patient.index,
   i in index_set(patient.workload_produced)],
  [workload | occupant in occupants, workload in occupant.workload_produced] ++
  [workload | patient in patients, workload in patient.workload_produced]
);

var int: total_excess_nurse_workload =
  sum(nurse in nurses, d in DAYS, s in SHIFTS where nurse_is_scheduled(nurse, d, s))(
    max(
      0,
      sum(r in ROOMS)(
        if nurse_assignments[r, d, s] == nurse.index
        then room_workloads[r, d, s]
        else 0
        endif
      ) - nurse_capacity(nurse, d, s)
    )
  );


%% S5 Open OTs: The number of OTs opened on each day should be minimized.
%% Note that if an OT has no patients assigned for a particular day, it should
%% not open on that day.

int: NO_OT_ASSIGNMENT = min(OPERATING_THEATERS) - 1;

array[PATIENTS, DAYS] of var NO_OT_ASSIGNMENT..max(OPERATING_THEATERS): ot_assignment_matrix;

constraint forall(patient in patients, p = patient.index, d in DAYS)(
  ot_assignment_matrix[p, d] =
    if patient.surgery_release_day <= d /\
       (not patient.mandatory \/ d <= patient.surgery_due_day) /\
       patient.surgery_duration <= surgeon(patient).max_surgery_time[d]
    then (if admission_days[p] == d then ot_assignments[p] else NO_OT_ASSIGNMENT endif)
    else NO_OT_ASSIGNMENT
    endif
);

var int: total_opened_ots = (
  sum(d in DAYS)(nvalue([NO_OT_ASSIGNMENT] ++ [ot_assignment_matrix[p, d]| p in PATIENTS])) - card(DAYS)
);


%% S6 Surgeon transfer: The number of different OTs a surgeon is assigned to per
%% working day should be minimized.

var int: surgeon_transfer = sum(surgeon in surgeons, d in DAYS where surgeon.max_surgery_time[d] > 0)(
  max(
    0,
    nvalue(
      [NO_OT_ASSIGNMENT] ++
      [ot_assignment_matrix[p, d]| p in PATIENTS where patients[p].surgeon_id == surgeon.id]
    ) - 2
  )
);


%% S7 Admission delay: The number of days between a patient’s release date and
%% their actual date of admission should be minimized.

var int: total_admission_delay = sum(p in PATIENTS)(
    if admission_days[p] > max(DAYS) then 0 else admission_days[p] - patients[p].surgery_release_day endif
);


%% S8 Unscheduled patients: The number of optional patients who are not admitted
%% in the current scheduling period should be minimized.

var int: unscheduled_patients = sum(p in PATIENTS)(admission_days[p] > max(DAYS));


%% Objective

var int: objective = sum([
  weights.room_mixed_age * total_age_group_differences,
  weights.nurse_eccessive_workload * total_excess_nurse_workload,
  weights.room_nurse_skill * total_skill_level_deviation,
  weights.continuity_of_care *  total_discontinuity_of_care,
  weights.open_operating_theater * total_opened_ots,
  weights.surgeon_transfer * surgeon_transfer,
  weights.patient_delay * total_admission_delay,
  weights.unscheduled_optional * unscheduled_patients
]);

% solve
%   :: warm_start(
%       admission_days,
%       [if patients[p].mandatory then patients[p].surgery_release_day else days + 1 endif | p in PATIENTS])
%   minimize objective;

solve :: seq_search([
  int_search(nurse_assignments, first_fail, indomain_min),
  int_search(admission_days ++ room_assignments ++ ot_assignments, first_fail, indomain_min)
]) minimize objective;

output [
  showJSON(
    (
      'room-age-mix': total_age_group_differences,
      'excessive-nurse-workload': total_excess_nurse_workload,
      'room-skill-level': total_skill_level_deviation,
      'continuity-of-care': total_discontinuity_of_care,
      'opened-operating-theaters': total_opened_ots,
      'surgeon-transfer': surgeon_transfer,
      'patient-delay': total_admission_delay,
      'optional-unscheduled-patients': unscheduled_patients,
      'nurse-utilization':
        sum(nurse in nurses, r in ROOMS, d in DAYS, s in SHIFTS where nurse_assignments[r, d, s] == nurse.index)(room_workloads[r, d, s]) /
        sum(nurse in nurses, working_shift in nurse.working_shifts)(working_shift.max_load),
      'room-utilization':
        (sum(occupant in occupants)(card((min(DAYS)..(min(DAYS) + occupant.length_of_stay - 1)) intersect DAYS)) +
         sum(patient in patients)(
          card((admission_days[patient.index]..(admission_days[patient.index] + patient.length_of_stay - 1)) intersect DAYS))) /
        (card(DAYS) * sum(room in rooms)(room.capacity)),
      'surgeon-utilization':
        sum(patient in patients where admission_days[patient.index] in DAYS)(patient.surgery_duration) /
        sum(surgeon in surgeons)(sum(surgeon.max_surgery_time)),
      'operating-theater-utilization':
        sum(patient in patients where admission_days[patient.index] in DAYS)(patient.surgery_duration) /
        sum(operating_theater in operating_theaters, availability in operating_theater.availability)(availability)
    )
  )
];
