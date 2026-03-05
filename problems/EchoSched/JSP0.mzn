% Modifications by MiniZinc Challenge Organizers:
% - Modify search annotation to allow running in FD
% - Name objective variable `objective`
% - Fix redundant constraint to be hard constraint

% sets
set of int: JOBS;
set of int: MACHINES;
int: SPEED;

% data
array[JOBS,MACHINES,1..SPEED] of int: time;
array[JOBS,MACHINES,1..SPEED] of int: energy;
array[JOBS,MACHINES] of int: precedence;

% variables
array[JOBS,MACHINES] of var 0..sum(time): start_time :: output;
array[JOBS,MACHINES] of var 1..SPEED: SpeedScaling :: output;


constraint forall(j in JOBS, p in MACHINES, s in MACHINES where p != s)(
  if precedence[j,p] > precedence[j,s] then
      start_time[j,p] >= start_time[j,s] + time[j,s,SpeedScaling[j,s]]
  else
      start_time[j,s] >= start_time[j,p] + time[j,p,SpeedScaling[j,p]]
  endif
);


constraint forall(j1 in JOBS, j2 in JOBS, m in MACHINES where j1 < j2)(
  %redundant_constraint (start_time[j1,m] + time[j1,m,SpeedScaling[j1,m]] <= start_time[j2,m] \/ start_time[j2,m] + time[j2,m,SpeedScaling[j2,m]] <= start_time[j1,m]
  (start_time[j1,m] + time[j1,m,SpeedScaling[j1,m]] <= start_time[j2,m] \/ start_time[j2,m] + time[j2,m,SpeedScaling[j2,m]] <= start_time[j1,m]
));


var int: makespan :: output                    = max([start_time[j,m] + time[j,m,SpeedScaling[j,m]] | m in MACHINES, j in JOBS]);
var int: consumedEnergy :: output              = sum(m in MACHINES, j in JOBS) (energy[j,m,SpeedScaling[j,m]]);

var int: objective = makespan + consumedEnergy;

% solve :: int_search(
%      [makespan,consumedEnergy],
%      input_order,
%      indomain_min,
%      complete
%    )
%    minimize objective;

solve :: int_search(
  array1d(start_time) ++ array1d(SpeedScaling),
  first_fail,
  indomain_min
) minimize objective;
