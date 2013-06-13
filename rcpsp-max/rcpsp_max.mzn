%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2010 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
% Model example for Resource-constrained Project Scheduling Problems with
% minimal and maximal time lags (RCPSP/max)
%
% A RCPSP/max consists of resources, activities, and start-to-start constraints
% between some activities where resources have a specific resource capacity and
% activities require some of the capacities from some resources for their exe-
% cution.
%
% Here, we consider renewable resource with a discrete resource capacity and
% non-premptive activities with a discrete start time, duration, and resource
% requirements.
%
% The objective is to find an optimal schedule minimizing the project duration
% that respects the resource constraints (no resource overload exists at any 
% point in time) and start-to-start constraints.
% 
% Complexity note:
% Already the decision variant of RCPSP/max is NP-hard due to the fact that the
% start-to-start constraints which are difference (seperation) constraints.
%
%-----------------------------------------------------------------------------%

include "globals.mzn";

%-----------------------------------------------------------------------------%
% Parameters.
%-----------------------------------------------------------------------------%

int: n_res;     % The number of resources
int: n_tasks;   % The number of activities
int: n_dc;      % The number of difference constraints

set of int: Res   = 1..n_res;       % The set of resources
set of int: Tasks = 1..n_tasks;     % The set of activities
set of int: DCIdx = 1..n_dc;        % The index set of difference constraints

array [Res]         of int: rcap;   % The resource capacities
array [Tasks]       of int: dur;    % The task durations
array [Res, Tasks]  of int: rr;     % The task resource requirements
array [DCIdx, 1..3] of int: dcons;  % The difference constraints of form
                                    %   x + c <= y

    % Trivial upper bound for the project duration
int: t_max = sum(i in Tasks) (
                max(
                    [dur[i]] ++
                    [ dcons[idx, 2] 
                        | idx in DCIdx where dcons[idx, 1] == i]
                )
            );

set of int: Times = 0..t_max;       % The set of point in times

%-----------------------------------------------------------------------------%
% Variables.
%-----------------------------------------------------------------------------%

    % The task start times
array [Tasks] of var Times: s;

    % The project duration (makespan)
var Times: objective;

%-----------------------------------------------------------------------------%
% Constraints.
%-----------------------------------------------------------------------------%

    % Difference constraints
constraint
    forall (idx in DCIdx) (
        s[dcons[idx, 1]] + dcons[idx, 2] <= s[dcons[idx, 3]]
    );

    % Redundant non-overlapping (dijunctive) constraints
constraint
    forall (i, j in Tasks where i < j) (
        if exists(res in Res where rr[res, i] + rr[res, j] > rcap[res])(true) then
                % Activities i, and j cannot run in parallel
            if  exists( 
                    idx in DCIdx 
                where 
                    (   dcons[idx, 1] == i /\ dcons[idx, 3] == j
                    /\  dcons[idx, 2]  < dur[i] /\ dcons[idx, 2] > -dur[j] )
                ) (true)
            then
                    % Activity j must be run after i
                s[i] + dur[i] <= s[j]
            else if  exists( 
                    idx in DCIdx 
                where 
                    (   dcons[idx, 1] == j /\ dcons[idx, 3] == i
                    /\  dcons[idx, 2]  < dur[j] /\ dcons[idx, 2] > -dur[i] )
                ) (true)
            then
                    % Activity i must be run after j
                s[j] + dur[j] <= s[i]
            else
                    % Activity i must be run before or after j
                let {
                    var bool: b
                } in (
                    (     b  -> s[i] + dur[i] <= s[j] )
                /\  ( not(b) -> s[j] + dur[j] <= s[i] )
                )
            endif endif
        else
            true
        endif
    );

    % Cumulative resource constraints
constraint
   forall (res in Res) (
      cumulative( 
         s, 
         dur, 
         [ rr[res, i] | i in Tasks ], 
         rcap[res] 
      )
   );

    % Objective constraints
constraint
   forall (i in Tasks) (
      s[i] + dur[i] <= objective
   );

%-----------------------------------------------------------------------------%
% Search.
%-----------------------------------------------------------------------------%

solve
   :: int_search( s, first_fail, indomain_min, complete )
   minimize objective;

%-----------------------------------------------------------------------------%
% Output.
%-----------------------------------------------------------------------------%

output [
   "% rcpsp_max\n",
   "s = ",
   show( s ),
   ";\n",
   "objective = ",
   show( objective ),
   ";\n"
];

%-----------------------------------------------------------------------------%
% EOF.
%-----------------------------------------------------------------------------%

