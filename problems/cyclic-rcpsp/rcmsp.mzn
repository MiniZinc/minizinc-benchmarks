%------------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%------------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%------------------------------------------------------------------------------%
% Model example for Resource-Constrained Modulo Scheduling Problems (RCMSP)
% 
% RCMSP is a cyclic resource-constrained project scheduling problem with 
% generalised precedence relations  constrained to scarce cumulative resources 
% and tasks which are repeated infinitely. These tasks need some resource units 
% from the resource for their executions, but the resource cannot be overloaded
% at any point in time. Moreover, the tasks have an unit durations, except the
% artificial source and sink tasks which have a zero duration.
% The factor which a task is repeated is called period. Here, the periods of
% all tasks are the same.
%
% The generalised precedence relations, i.e., minimal and maximal time lags, are
% of form of s[i, k] + lat[i, j] <= s[j, k + w[i,j]], where s[i, k] is the
% start time of task i in the k's iteration, lat[i, j] is the latency between
% task i and task j, and w[i, j] is the distance between task i and task j.
% 
% The objective is to find a cyclic schedule that first minimizes the
% schedule period and then the makespan.
% 
%------------------------------------------------------------------------------%

include "cumulative.mzn";

%------------------------------------------------------------------------------%
% Model parameters.


    % Resources
    %
int: n_res;                         % Number of resources
set of int: Res = 1..n_res;         % Identifiers of the resources
array [Res] of int: rcap;           % Resource capacities

    % Tasks where the first task represents the start of the schedule and the
    % last task the end of the schedule
    %
int: n_tasks;                       % Number of tasks
set of int: Tasks = 1..n_tasks;     % Identifiers of the tasks
array [Tasks] of int: d =           % Durations of the tasks
    [ if i in {1, n_tasks} then 0 else 1 endif | i in Tasks ];
array [Tasks, Res] of int: rreq;    % Resource requirements of the tasks

    % Generalised Precedence Constraints
    %
int: n_prec;                        % Number of precedence relations
set of int: Prec = 1..n_prec;       % Identifiers of the precedence relations
array [Prec, 1..4] of int: prec;    % 2D-array of precedence relations
                                    %   prec[., 1] - Identifier of task t1
                                    %   prec[., 2] - identifier of task t2
                                    %   prec[., 3] - Precedence latency
                                    %   prec[., 4] - Precedence distance

    % Time Periods and Iterations
    %
int: t_max =                        % Maximal period
    sum(i in Prec where prec[i, 3] > 0)(prec[i, 3]);
set of int: Times = 0..t_max;       % Time periods
set of int: Iters = 0..n_tasks;     % Iterations

%-----------------------------------------------------------------------------%
% Model variables.

array [Tasks] of var Times: s;      % Start time variables
array [Tasks] of var Iters: k;      % Iteration variables
    
    % Makespan of the one iteration
    %
var Times: makespan = 
    max([ s[i] - k[i] * s[n_tasks] | i in Tasks where i > 0 /\ i < n_tasks ])
    - min([ s[i] - k[i] * s[n_tasks] | i in Tasks where i > 0 /\ i < n_tasks ])
    + 1;

    % The objective:
    %   1. minimize the period of the schedule, i.e., "s[n_tasks]"
    %   2. minimize the makespan of one iteration, i.e., "makespan"
var 0.. (t_max * (1 + t_max)): objective =
    s[n_tasks] * t_max + makespan;

%-----------------------------------------------------------------------------%
% Constraints.

    % Generalised Precedence Constraints
    %
constraint
    forall(i in Prec)(
        let { var bool: b } in (
            ( b <-> ( s[prec[i,1]] + prec[i,3] <= s[prec[i,2]] ) )
        /\  k[prec[i,1]] + bool2int(not(b)) <= k[prec[i,2]] + prec[i,4]
        )
    );

    % Redundant non-overlapping constraints
    %
constraint
    forall(i, j in Tasks where i < j)(
        if exists(r in Res)(rreq[i, r] + rreq[j, r] > rcap[r]) then
		    s[i] + d[i] <= s[j]	 \/  s[j] + d[j] <= s[i] 
        else
            true
        endif
    );

    % Cumulative resource constraints
    %
constraint
    forall(r in Res)(
        let { 
                % Tasks that running on this resource
            set of int: ResTasks = 
                { i | i in Tasks where rreq[i, r] > 0 /\ d[i] > 0 },
            int: sum_rreq = sum([0] ++ [rreq[i, r] | i in ResTasks])
        } in (
            % Check whether all tasks can concurrently run on this resource
            if sum_rreq <= rcap[r] then
                true
            else
                cumulative(
                    [ s[i]       | i in ResTasks ],
                    [ d[i]       | i in ResTasks ],
                    [ rreq[i, r] | i in ResTasks ],
                    rcap[r]
                )
            endif
        )
    );

    % Period constraints
    %
constraint
    k[n_tasks] = max([ k[i] | i in Tasks where i < n_tasks])
/\  forall(i in Tasks where i < n_tasks)(
        s[i] + d[i] <= s[n_tasks]
    );

    % Symmetry breaking constraint
    %
constraint
    s[1] = 0 /\ k[1] = 0;

%-----------------------------------------------------------------------------%
% Objective.

solve
   :: search
   minimize objective;

ann: search = seq_search([
        assign_start_times,
        assign_iters
    ]);

ann: assign_start_times = int_search( s, smallest, indomain_min, complete );
ann: assign_iters = int_search(k, smallest, indomain_min, complete );

%-----------------------------------------------------------------------------%
% Output

output [
   "% rcmsp\n",
   "s = " ++ show( s ) ++ ";\n",
   "k = " ++ show( k ) ++ ";\n",
   "constraint makespan = " ++ show( makespan ) ++ ";\n",
   "constraint objective = " ++ show( objective ) ++ ";\n"
];

%-----------------------------------------------------------------------------%
%%% EOF %%%

