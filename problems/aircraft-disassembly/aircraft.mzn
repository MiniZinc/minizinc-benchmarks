% Author: Allen Zhong 2022 
% Aircraft Disassembly Scheduling
% Constraint Programming model
% The model is inspired by the following models:
%  - the CP Optimizer model for Aircraft Disassembly Scheduling from https://github.com/cftmthomas/AircraftDisassemblyScheduling 
%  - the MiniZinc model for Multi-Skill Project Scheduling Problem from https://github.com/youngkd/MSPSP-InstLib 
  
include "cumulative.mzn";
include "disjunctive.mzn";
% include "redefinitions.mzn";

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%
% INSTANCE INITIALISATION
int: nActs;
int: nResources;
int: nSkills;
int: nPrecs;
int: nUnavailable;
int: nUnrels; % number of unrelated activites wrt to the precedence graph
int: maxt;  % maximum makespan

set of int: ACT = 1..nActs;
set of int: RESOURCE = 1..nResources;
set of int: SKILL = 1..nSkills;
set of int: PREC = 1..nPrecs;
set of int: UNREL = 1..nUnrels;
set of int: TIME = 0..maxt;
set of int: UNAVAILABLE = 1..nUnavailable; 

array[ACT] of set of RESOURCE: USEFUL_RES; % useful resources for each act
array[RESOURCE] of set of ACT: POTENTIAL_ACT; % potential activities for each res

array[ACT] of int: dur; % duration
array[ACT,SKILL] of int: sreq; % task's skill requirement
array[RESOURCE,SKILL] of bool: mastery; % resource's skill mastery
array[RESOURCE] of int: resource_cost; % cost of resource per period 
array[PREC] of ACT: pred; % predecessor activity
array[PREC] of ACT: succ; % successor activity
array[UNREL] of ACT: unpred; % unrelated predecessor activity
array[UNREL] of ACT: unsucc; % unrelated successor activity
array[SKILL] of 0..nResources: scap = [sum(r in RESOURCE)(bool2int(mastery[r,s])) | s in SKILL]; % capacity of each skill
array[UNAVAILABLE] of RESOURCE: unavailable_resource; 
array[UNAVAILABLE] of TIME: unavailable_start;  
array[UNAVAILABLE] of TIME: unavailable_end; 

% producer/consumer constraint 
array[ACT] of int: mass; % mass required by different activities 
set of int: M; % set of mass required to be balanced 
array[M, 1..2] of set of LOC: comp_prod; % the producer and consumer location of mass 
array[M] of int: maxDiff; % maximum difference of mass 

% amount of mass removed from the balance  
array[M, ACT] of int: consumption = array2d(M, ACT, [ if loc[j] in comp_prod[i, 1] then mass[j] else if loc[j] in comp_prod[i, 2] then -mass[j] else 0 endif endif | i in M, j in ACT]); 
array [M] of set of int: resAct = [ {i | i in ACT where consumption[m, i] != 0} | m in M];  % set of "non-zero" activities for each mass balanced

% Location constraint 
int: nLocations; 
set of int: LOC = 1..nLocations;
array[ACT] of LOC: loc; % location of activities  
array[LOC] of int: loc_cap; % capacity of locations 
array[ACT] of int: occupancy; % occupancy requirement 

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%
% DECISION VARIABLES
array[ACT] of var TIME: start; % start time
array[ACT,RESOURCE] of var bool: assign; % assignment of resources to activities
array[ACT,RESOURCE,SKILL] of var bool: contrib; % skill contribution assignment
array[UNREL] of var bool: overlap; % overlapping of unrelated activities 

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%
% CONSTRAINTS

% Precedence constraint
constraint forall(p in PREC)(
    start[pred[p]] + dur[pred[p]] <= start[succ[p]]
);

% Unary resource constraint
constraint
  forall ( 
    u in UNREL
  )(
  let {int: i = unpred[u],
       int: j = unsucc[u]} in
        if exists( s in SKILL )( sreq[i,s] + sreq[j,s] > scap[s] ) then
             (     overlap[u]  -> start[i] + dur[i] <= start[j] ) /\
             ( not(overlap[u]) -> start[j] + dur[j] <= start[i] )
        else
            (
              not(overlap[u]) <-> (start[i] + dur[i] <= start[j] \/
                                   start[j] + dur[j] <= start[i])
            ) /\ (
              forall(
                r in USEFUL_RES[i] intersect USEFUL_RES[j]
              )(
                (assign[i,r] /\ assign[j,r]) -> not(overlap[u])
              )
            )
        endif
  );

% Resource unavailable constraint 
constraint forall(i in UNAVAILABLE)(
  forall(a in ACT)(
    assign[a, unavailable_resource[i]] -> (start[a] + dur[a] <= unavailable_start[i] \/ start[a] >= unavailable_end[i])
  )
);

% Skill constraint: Skill requirements are satisfied
constraint forall(a in ACT, s in SKILL where sreq[a,s]>0)(
  sum(r in USEFUL_RES[a])(contrib[a,r,s]) == sreq[a,s]
);

% Non-Multi-Tasking constraint: Maximum of one contribution by each activity
constraint forall(a in ACT, r in USEFUL_RES[a])(
  sum(s in SKILL where mastery[r,s]==true /\ sreq[a,s]>0)
     (contrib[a,r,s]) <= 1
);

% Skill constraint: Resources only use skills they have mastered
constraint forall(a in ACT, r in USEFUL_RES[a], s in SKILL)(
  contrib[a,r,s] <= bool2int(mastery[r,s])
);

% Linking constraint: resources only contribute to activities they are assigned
constraint forall(a in ACT, r in USEFUL_RES[a], s in SKILL where sreq[a,s]>0) (
  contrib[a,r,s] <= bool2int(assign[a,r])
);

% Location constraint: limit the maximum number of technicians allowed to work there at the same time.
constraint forall(i in LOC)(cumulative(start, dur, occupancy, loc_cap[i]));

% order variables describe the relative precedence between pairs of activities 
array[ACT, ACT] of var bool: act_leq_act = array2d(ACT, ACT, [start[i] <= start[j] | i, j in ACT]); 

% constraint for correct reservoir levels at the start of activities 
constraint forall(m in M, i in resAct[m])(
		sum(j in resAct[m])( consumption[m, j] * act_leq_act[j, i] ) <= maxDiff[m] 
	/\ 	sum(j in resAct[m])( consumption[m, j] * act_leq_act[j, i] ) >= -maxDiff[m] 
); 

% constraint for act_leq_act 
constraint forall(i, j in ACT where i < j)( act_leq_act[i, j] \/ act_leq_act[j, i]); 

% minimize the makespan
var int: objective = 100000 * max(start) + sum(a in ACT, r in RESOURCE)(resource_cost[r] * dur[a] * assign[a, r]); 
solve :: seq_search([
  int_search(start, input_order, indomain_min),
  bool_search(array1d(assign) ++ array1d(contrib) ++ overlap, input_order, indomain_min)
]) minimize objective;
