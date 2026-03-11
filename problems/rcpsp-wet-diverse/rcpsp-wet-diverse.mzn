%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2016 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
% Model example for Resource-Constrained Project Scheduling Problems with
% Weighted Earliness/Tardiness objective (RCPSP/WET)
%
% A RCPSP consists of resources, tasks, and precedences between some tasks
% where resources have of a specific capacity and tasks need some capacity of
% some resource to be executed.
% Here, we consider resources with a constant discrete capacity over time and
% tasks with a constant discrete duration and resource requirements.
% The objective is to find a optimal schedule so that tasks start as close as
% possible to the given start time for each task, penalizing earliness or
% tardiness according to the given weight for earliness and tardiness per task.
%
%-----------------------------------------------------------------------------%

include "cumulative.mzn";
%-----------------------------------------------------------------------------%
% Model parameters.


    % Resources
    %
int: n_res;                     % The number of resources
set of int: Res = 1..n_res;     % The set of all resources
array [Res] of int: rc;         % The resource capabilities

    % Tasks
    %
int: n_tasks;                           % The number of tasks
set of int: Tasks = 1..n_tasks;         % The set of all tasks
array [Tasks]      of int       : d  ;  % The task durations
array [Res, Tasks] of int       : rr ;  % The resource requirements
array [Tasks]      of set of int: suc;  % The task successors

    % Deadlines
    %
    % deadline[i, 1] is the desired start time for task i,
    % deadline[i, 2] is the earliness cost per time unit of earliness,
    % deadline[i, 3] is the tardiness cost per time unit of tardiness.
array [Tasks, 1..3] of int: deadline;

    % Planning horizon
    %
    % Note that our RCPSP/WET instance generator requires a solution to the
    % equivalent RCPSP problem in order to generate the instances, so it gives
    % us a planning horizon = the makespan of the RCPSP problem, plus 20% slop
int: t_max; %= sum(i in Tasks)(d[i]);     % End time of the planning horizon
set of int: Times = 0..(t_max - 1);     % Possible start times

function array[int] of var int: model(int: instance) =
let {
  %-----------------------------------------------------------------------------%
  % Model variables.

%  array [Tasks] of var Times: s;  % The start times

  %-----------------------------------------------------------------------------%
  % Constraints.

    % Precedence constraints
    %
constraint
   forall ( i in Tasks, j in suc[i] )
   (
         st[instance,i] + d[i] <= st[instance,j]
   );

    % Redundant non-overlapping constraints
    %
constraint
    redundant_constraint(
        forall ( i, j in Tasks where i < j )
        (
            if exists(r in Res)(rr[r, i] + rr[r, j] > rc[r]) then
                st[instance,i] + d[i] <= st[instance,j]   \/ st[instance,j] + d[j] <= st[instance,i]
            else
                true
            endif
        )
    );

    % Cumulative resource constraints
    %
constraint
    forall ( r in Res )
    (
        let {
            set of int: RTasks =
                            { i | i in Tasks
                            where rr[r, i] > 0 /\ d[i] > 0 },
            int: sum_rr = sum(i in RTasks)(rr[r, i])
        } in (
            if RTasks != {} /\ sum_rr > rc[r] then
                cumulative(
                    [ st[instance,i] | i in RTasks ],
                    [ d[i] | i in RTasks ],
                    [ rr[r, i] | i in RTasks ],
                    rc[r]
                )
            else
                true
            endif
        )
    );

  % Earliness
  var 0..sum(i in Tasks) (
      deadline[i, 2] * deadline[i, 1]
  ): earliness = sum (i in Tasks) (deadline[i, 2] * max(0, deadline[i, 1] - st[instance,i]));

  % Tardiness
  var 0..sum(i in Tasks) (
      deadline[i, 3] * (t_max - deadline[i, 1])
  ): tardiness = sum (i in Tasks) (deadline[i, 3] * max(0, st[instance,i] - deadline[i, 1]));

} in [earliness, tardiness];

%-----------------------------------------------------------------------------%
% Diversity.

% Number of solutions
int: nsols;
set of int: Solutions = 1..nsols;

% Decisions global
array[Solutions,Tasks] of var Times: st;

% Objectives for all solutions
array[1..2, Solutions] of var int: objectives :: add_to_output;
constraint forall (s in Solutions) (objectives[..,s] = model(s));

% Extreme points
int: emin;
int: emax;
int: tmin;
int: tmax;
constraint objectives[1,1] = emin;
constraint objectives[2,1] = tmax;
constraint objectives[1,2] = emax;
constraint objectives[2,2] = tmin;

% Check for dominance
predicate is_dominated(int: e, int: t, int: sol) =
  (objectives[1,sol] <= e) /\ (objectives[2,sol] <= t);

% Whether a point is dominated by a solution or not
array[emin..emax, tmin..tmax] of var bool: dominated;
constraint
  forall (e in emin..emax, t in tmin..tmax) (
    dominated[e,t] = exists (s in Solutions) (is_dominated(e,t,s)));

% A solution must not be dominated by any other solution
constraint
  forall (s1, s2 in Solutions where s1 != s2) (
    (objectives[1,s1] < objectives[1,s2]) \/ (objectives[2,s1] < objectives[2,s2]));

var 0..emax*tmax: objective = sum(dominated);

% Maximize the hypervolume: the number of dominated points
solve 
      :: int_search(array1d(st), smallest, indomain_min)
      maximize objective;

output [
    "st = array2d(\(Solutions), \(Tasks), \(st));\n",
    "objective = \(objective);\n"
];
