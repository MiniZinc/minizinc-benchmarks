include "nvalue_fn.mzn";

% DEPARTMENTS AND STATIONS
int: numDepartments; % number of departments to schedule
array[0..numDepartments] of string: departmentName; % Department names, ordered by infection chance (lowest first)
int: numStations; % total number of stations
array[0..numStations] of string: stationName;
array[0..numStations] of int: stationDepartment; % department for each station
array[0..numStations] of bool: stationCommon;

% PERSONNEL DATA
int: numPers; % number of persons to schedule
array[1..numPers] of string: personName;
int: numSkills; % number of skills
array[0..numSkills] of string: skillName;
array[1..numPers,0..numStations,0..numSkills] of int: stationPrefs; % weights for assigning personnel to stations and skills (0-3, lower is better, 4 is forbidden)
array[1..numPers] of bool: persRisk; % personal risk (1 is increased risk)
array[1..numPers] of int: persRobustness; % personell robustness (higher is better)
array[1..numPers] of bool: persRequireWork; % indicates that a person should work
array[1..numPers] of int: maxHoursWeek; % the maximum hours a person can work per week
array[1..numPers] of set of 1..numDays: forbiddenDays; % days on which a person cannot work (mostly for part-time)
array[1..numPers] of 0..numDays: histConsecutiveWorkDays; % the number of consecutive working days for a person at the end of the previous planning period
array[1..numPers] of 0..numStations: histLastStationWorked; % the last station on which a person has worked in the previous planning period
array[1..numPers] of 0..numShifts: histShiftLastDay; % the shift assigned to a person on the last day of the previous planning period

% SHIFT DATA
int: numShifts; % number of shifts
int: numDays; % days in the planning period
array[0..numShifts] of string: shiftName;
array[0..numShifts] of int: shiftLength; % length of shifts in hours
array[0..numShifts] of set of int: forbiddenSequences; % shifts that are forbidden after a certain shift

array[0..numStations,0..numShifts,1..numDays,0..numSkills] of int: demand; % demand per shift, day, station and skill

% SOFT CONSTRAINT WEIGHTS
int: preferenceWeight; % weight for assigning personnel to less fitting stations and skills
int: riskWeight; % weight for assigning personnel with high risk
int: rbWeight; % TODO how to weigh?
int: persWeight; % penalty for each working employee
int: stationWeight; % penalty for each station change

% INDICES FOR SPECIAL SHIFTS
% the standard shift has to be index 1, the extended shift subsuming the standard shift has to be index 2
set of int: indexNight; % night shift for night sequence constraint

% SUBSUMING SHIFTS
int: numSubsum;
array[1..numSubsum] of int: subDepartment;
array[1..numSubsum,1..numDays] of int: subDemand;
array[1..numSubsum] of set of int: subSkills;

% DECISION VARIABLES
array[1..numPers,1..numDays] of var 0..numShifts: assignShift; % 0..day off, otherwise assigned shift
array[1..numPers,1..numDays] of var 0..numSkills: assignSkill;
array[1..numPers,1..numDays] of var 0..numStations: assignStation;

constraint forall (i in 1..numPers, j in 1..numDays) (count([assignShift[i,j] = 0, assignStation[i,j] = 0, assignSkill[i,j] = 0]) in {0,3});

% max 6 consecutive days
constraint forall (i in 1..numPers) ( % history
  numDays < 7 \/ exists (k in 1..max(7-histConsecutiveWorkDays[i], 1)) (assignShift[i,k] = 0)
);
constraint forall (i in 1..numPers, j in 2..numDays-6) (
  exists (k in 0..6) (assignShift[i,j+k] = 0)
);
constraint forall (i in 1..numPers where assignShift[i,1] in indexNight) ( % history TODO can result in triple night shift, would need shift on day before as well
  count([histShiftLastDay[i] = assignShift[i,1], assignShift[i,2] = assignShift[i,1]]) = 1
);
constraint forall (i in 1..numPers, j in 2..numDays-1 where assignShift[i,j] in indexNight) (
  count([assignShift[i,j-1] = assignShift[i,j], assignShift[i,j+1] = assignShift[i,j]]) = 1
);

int: numWeeks = numDays div 7; % TODO assumes starting on Monday and numDays divisible by 7
% max hours per week
constraint forall (i in 1..numPers, j in 0..numWeeks-1) ( 
  sum (k in 1..7) (shiftLength[assignShift[i,7*j+k]]) <= maxHoursWeek[i]
);
% Shifts 1 and 2: individual assignment on common stations
constraint forall (i in 1..numStations where stationCommon[i], j in 1..2, k in 1..numDays, l in 1..numSkills) (
  count (m in 1..numPers) (assignShift[m,k] = j /\ assignStation[m,k] = i /\ assignSkill[m,k] = l) = demand[i,j,k,l]
);
% Shift 1 may be subsumed by shift 2 on non-common stations
constraint forall (i in 1..numStations where not stationCommon[i], k in 1..numDays, l in 1..numSkills) (
  count (m in 1..numPers) (assignShift[m,k] in {1,2} /\ assignStation[m,k] = i /\ assignSkill[m,k] = l) = demand[i,1,k,l]
);
% Shifts 3+: regular assignment
constraint forall (i in 1..numStations, j in 3..numShifts, k in 1..numDays, l in 1..numSkills) (
  count (m in 1..numPers) (assignShift[m,k] = j /\ assignStation[m,k] = i /\ assignSkill[m,k] = l) = demand[i,j,k,l]
);
% redundant constraint that checks for each skill if enough employees are scheduled that have prefs < 4
constraint forall (i in 1..numStations, j in 1..numShifts where j != 2 \/ stationCommon[i], k in 1..numDays, l in 1..numSkills) (
  count (m in 1..numPers) (
    if j = 1 /\ not stationCommon[i] then
      assignShift[m,k] = 1 \/ assignShift[m,k] = 2
    else 
      assignShift[m,k] = j 
    endif /\
    assignStation[m,k] = i /\
    stationPrefs[m,i,l] < 4
  ) >= demand[i,j,k,l]
);
% demand for subsuming stations, hardcoded to shift index 2
constraint forall (i in 1..numSubsum, j in 1..numDays) (
  count (k in 1..numPers) (
    assignShift[k,j] = 2 /\ stationDepartment[assignStation[k,j]] = subDepartment[i] /\ not stationCommon[assignStation[k,j]] /\ assignSkill[k,j] in subSkills[i]
  ) = subDemand[i,j]
);

% only assign allowed skill and station combination
constraint forall (i in 1..numPers, j in 1..numDays) (
  stationPrefs[i, assignStation[i,j], assignSkill[i,j]] < 4
);
% forbidden shift sequences
constraint forall (i in 1..numPers, j in 1..numDays-1) (
  not (assignShift[i,j+1] in forbiddenSequences[assignShift[i,j]])
);
% forbidden sequence for last history shift
constraint forall (i in 1..numPers) (
  not (assignShift[i,1] in forbiddenSequences[histShiftLastDay[i]])
);
% forbidden days
constraint forall (i in 1..numPers, j in forbiddenDays[i]) (
  assignShift[i,j] = 0
);

% helper variables whether a person is working at all
array[1..numPers] of var bool: isWorking = [exists (j in 1..numDays) (assignShift[i,j] > 0) | i in 1..numPers];
% persons from reserve should work now (if history is given)
constraint forall (i in 1..numPers) (persRequireWork[i] -> isWorking[i]);

% helper variables for last assigned station
array[1..numPers,0..numDays] of var 0..numStations: lastStation;
% history for assigned station, history station should only be common if there was no specific station assigment in the whole period
constraint forall (i in 1..numPers) (
  lastStation[i,0] = if stationCommon[histLastStationWorked[i]] then 0 else histLastStationWorked[i] endif
);
% track last assigned station
constraint forall (i in 1..numPers, j in 1..numDays) (
  lastStation[i,j] = if stationCommon[assignStation[i,j]] then lastStation[i,j-1] else assignStation[i,j] endif
);

% count changes (unless there was no previous station)
var 0..numPers*numDays: stationChanges = count (i in 1..numPers, j in 1..numDays) (
  lastStation[i,j-1] > 0 /\ lastStation[i,j] != lastStation[i,j-1]
);

% no different departments (could transform to soft constraint)
constraint forall (i in 1..numPers) (
  nvalue([stationDepartment[histLastStationWorked[i]]] % history
    ++ [stationDepartment[assignStation[i,j]] | j in 1..numDays]) <= 2
);

% number of working persons
var 0..numPers: workingPers = count (i in 1..numPers) (isWorking[i]);
% sum of preference weights
var 0..3*numPers*numDays: preferences = sum (i in 1..numPers, j in 1..numDays) (
  stationPrefs[i, assignStation[i,j], assignSkill[i,j]]
);
% persons at risk that are working, weighted by department
var 0..numPers*numDepartments: workingRisk = sum (i in 1..numPers where persRisk[i] /\ isWorking[i]) (
  stationDepartment[lastStation[i,numDays]]
);

var int: objective = workingPers * persWeight + preferences * preferenceWeight + workingRisk * riskWeight + stationChanges * stationWeight;

solve :: search2
  minimize objective;

ann : search2 = seq_search([ int_search([[assignShift[p,d],
                                         assignStation[p,d],
                                         assignSkill[p,d]][k] | p in 1..numPers, k in 1..3],
                            smallest,
                            indomain_min,
                            complete)
                          | d in 1..numDays ]);

output["{\n"];
output["\t \"objective\" : " ++ show(objective) ++ ",\n"];
output["\t \"objectiveDetails\" : " ++ show([workingPers, preferences, workingRisk, stationChanges]) ++ ",\n"];
output["\t \"stationDepartment\" : " ++ show([ stationDepartment[s] | s in 1..numStations]) ++ ",\n"];
output["\t \"personNames\" : " ++ show(personName) ++ ",\n"];
output["\t \"shiftNames\" : " ++ show(shiftName) ++ ",\n"];
output["\t \"stationNames\" : " ++ show(stationName) ++ ",\n"];
output["\t \"departmentNames\" : " ++ show(departmentName) ++ ",\n"];
output["\t \"skillNames\" : " ++ show(skillName) ++ ",\n"];
output["\t \"assignShift\" : [" ++ join(", ", [ show([ fix(assignShift[i,j]) | j in 1..numDays ]) | i in 1..numPers ]) ++ "],\n"];
output["\t \"assignStation\" : [" ++ join(", ", [ show([ fix(assignStation[i,j]) | j in 1..numDays ]) | i in 1..numPers ]) ++ "],\n"];
output["\t \"assignSkill\" : [" ++ join(", ", [ show([ fix(assignSkill[i,j]) | j in 1..numDays ]) | i in 1..numPers ]) ++ "]\n"];
output["}\n"];

include "global_cardinality_low_up.mzn";

constraint forall(d in 1..numDays)(
  global_cardinality_low_up([ assignShift[p,d] | p in 1..numPers ], 
    [ s | s in 0..numShifts ],
    [ 
      numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))), 
      sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,1,d,k])) - sum(t in 1..numSubsum)(subDemand[t,d]),
      sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,2,d,k])) + sum(t in 1..numSubsum)(subDemand[t,d])
    ] ++ [ sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,s,d,k])) | s in 3..numShifts ],
    [ 
      numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))), 
      sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,1,d,k])) - sum(t in 1..numSubsum)(subDemand[t,d]),
      sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,2,d,k])) + sum(t in 1..numSubsum)(subDemand[t,d])
    ] ++ [ sum(t in 1..numStations)(sum(k in 1..numSkills)(demand[t,s,d,k])) | s in 3..numShifts ]
    )
);

constraint forall(d in 1..numDays)(
  global_cardinality_low_up([ assignStation[p,d] | p in 1..numPers ], 
    [ s | s in 0..numStations ],
    [ numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))) ] ++ [ sum(t in 1..numShifts)(sum(k in 1..numSkills)(demand[s,t,d,k])) | s in 1..numStations ],
    [ numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))) ] ++ [ sum(t in 1..numShifts)(sum(k in 1..numSkills)(demand[s,t,d,k])) | s in 1..numStations ]
    )
);

constraint forall(d in 1..numDays)(
  global_cardinality_low_up([ assignSkill[p,d] | p in 1..numPers ], 
    [ s | s in 0..numSkills ],
    [ numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))) ] ++ [ sum(t in 1..numStations)(sum(k in 1..numShifts)(demand[t,k,d,s])) | s in 1..numSkills ],
    [ numPers - sum(t in 1..numStations)(sum(s in 1..numShifts)(sum(k in 1..numSkills)(demand[t,s,d,k]))) ] ++ [ sum(t in 1..numStations)(sum(k in 1..numShifts)(demand[t,k,d,s])) | s in 1..numSkills ]
    )
);