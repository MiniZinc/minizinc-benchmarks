%-----------------------------------------------------------------------------%
% Resource Availability Cost Problem (also known as Resource Investment Problem)
%
% The problem consists of a set of tasks having some precedence relations 
% between them and requiring some resource from scarce renewable resource
% having a different availability cost per unit. The goal is to complete all
% tasks in the given planning horizon, so that the resource availability
% cost is minimised. Note that cost per unit does not depend on its 
% utilisation!
%
% This simple model was derived from the model presented in this publication:
%
%   Stefan Kreter, Andreas Schutt, Peter J. Stuckey, Jürgen Zimmermann (2018): 
%   Mixed-integer Linear Programming and Constraint Programming Formulations 
%   for Solving Resource Availability Cost Problems. European Journal of 
%   Operational Research, Volume 266, Issue 2, pages 472-486. 2018.
%   https://doi.org/10.1016/j.ejor.2017.10.014
%
% Submitter: Andreas Schutt
%
%-----------------------------------------------------------------------------%
% MiniZinc Version Requirement

    % Note that at least version 2.1.7 is required due to a bug in the
    % evaluation of recursive functions in previous versions.
mzn_min_version_required = 21007;   

%-----------------------------------------------------------------------------%
% Includes

include "cumulative.mzn";

%-----------------------------------------------------------------------------%
% Parameters
    
    % Resources
    %
int: n_res;                     % The number of resources
set of int: Res = 1..n_res;     % The set of resources
array [Res] of int: cost;       % The unit cost of resources
array [Res] of int: lb_usage =  % Trivial lower bound on the resource demand
    [ max(i in Tasks)(rr[r, i]) | r in Res ];
array [Res] of int: ub_usage =  % Trivial upper bound on the resource demand
    [ sum(i in Tasks)(rr[r, i]) | r in Res ];
array [Res] of int: lb_cost =   % Trivial lower bound on the resource cost
    [ cost[r] * lb_usage[r] | r in Res ];
array [Res] of int: ub_cost =   % Trivial upper bound on the resource cost
    [ cost[r] * ub_usage[r] | r in Res ];

    % Tasks
    %
int: n_tasks;                           % The number of tasks
set of int: Tasks = 1..n_tasks;         % The set of tasks
array [Tasks] of int: dur;              % The duration of tasks
array [Res, Tasks] of int: rr;          % The resource requirement of tasks
array [Tasks] of set of Tasks: succ;    % The (immediate) successors of tasks


    % Planning Horizon
    %
int: t_max;                     % End of the planning horizon
set of int: Times = 0..t_max;   % The planning horizon


%-----------------------------------------------------------------------------%
% Derived parameters and schedule

    % Tasks
    %
array [Tasks] of set of Tasks: prec =   % The (immediate) predecessors of tasks
    [ {j | j in Tasks diff all_succ[i] where i in succ[j]} | i in Tasks ];
array [Tasks] of set of Tasks: all_succ =   % All successors of tasks
    [ all_succs(i) | i in Tasks ];
array [Tasks] of set of Tasks: all_prec =   % All predecessors of tasks
    [ {j | j in Tasks diff all_succ[i]  where i in all_succ[j]} | i in Tasks ];
array [Tasks] of set of Tasks: unrelated =  % All unrelated tasks of tasks (no successor and no predecessor)
    [ Tasks diff all_succ[i] diff all_prec[i] diff {i} | i in Tasks ];

    % The earliest start time schedule
    %
array [Tasks] of Times: es = [ est(i) | i in Tasks ];

    % The maximal resource consumption for the earliest start time schedule
    %
array [Res] of int: rusage_es = 
    [ max(i in Tasks)(
        rr[r, i] + sum(j in unrelated[i] where overlap(es[i], dur[i], es[j], dur[j]))(rr[r, j])
      )
    | r in Res ];
    
    %  The latest completion time schedule
    %
array [Tasks] of Times: ls = [ lct(i) | i in Tasks ];

    % The maximal resource consumption for the latest completion time schedule
    %
array [Res] of int: rusage_ls = 
    [ max(i in Tasks)(
        rr[r, i] + sum(j in unrelated[i] where overlap(ls[i] - dur[i], dur[i], ls[j] - dur[j], dur[j]))(rr[r, j])
      )
    | r in Res ];

%-----------------------------------------------------------------------------%
% Variables.

    % The start times of tasks
    %
array [Tasks] of var Times: s;

    % The resource capacity/usage
    %
array [Res] of var min(lb_usage)..max(ub_usage): rcap;

    % The objective
    %
var sum(lb_cost)..sum(ub_cost): objective;

%-----------------------------------------------------------------------------%
% Auxiliary functions and tests

    % Computing all successors of a task
    % (Note that this is not an efficient computation of all successors for a
    % task and may take a long time for a large number of tasks.)
    %
function set of Tasks: all_succs(Tasks: i) = (
    let {
        array[int] of set of Tasks: all_succs_js = 
            [ all_succs(j) | j in succ[i] ];
    } in array_union(all_succs_js) union succ[i]
);

    % Test whether the executions of two tasks are overlapping
    %
test overlap(int: si, int: di, int: sj, int: dj) = (
    si < sj + dj /\ sj < si + di 
);

    % Computation of the earliest start time of a task in the earliest
    % start time schedule
    % (Note that this is not an efficient computation of the earliest
    % start time and may take a long time for a large number of tasks.)
    %
function Times: est(Tasks: i) = (
    let {
        array[int] of Times: all_prec_ect = [0] ++ [ est(j) + dur[j] | j in prec[i] ];
    } in
        max(all_prec_ect)
);

    % Computation of the latest completion time of a task in the latest
    % completion time schedule
    % (Note that this is not an efficient computation of the latest
    % completion time and may take a long time for a large number of 
    % tasks.)
    %
function Times: lct(Tasks: i) = (
    let {
        array[int] of Times: all_succ_lst = [t_max] ++ [ lct(j) - dur[j] | j in succ[i] ];
    } in
        min(all_succ_lst)
);

%-----------------------------------------------------------------------------%
% Constraints.

    % Restricting the bounds on the resource capacity
    %
constraint forall(r in Res)(
    lb_usage[r] <= rcap[r] /\ rcap[r] <= ub_usage[r] 
);

constraint forall(i in Tasks)(
    s[i] + dur[i] <= t_max
);

    % Precedence constraints
    %
constraint forall(i in Tasks, j in succ[i])(
    s[i] + dur[i] <= s[j]
);


    % Cumulative resource constraints
    % Note that this constraint will not bind the resource capacity variable!
constraint forall(r in Res)(
    cumulative(s, dur, [ rr[r, i] | i in Tasks ], rcap[r])
);

    % Redundant non-overlapping constraints
    % Seems to be not worhtwhile at least for Chuffed
constraint redundant_constraint(
    forall(i in Tasks, j in unrelated[i])(
        forall(r in Res where rr[r, i] + rr[r, j] > lb_usage[r])(
            (rr[r, i] + rr[r, j] > rcap[r]) -> (
                (s[i] + dur[i] <= s[j]) \/ (s[j] + dur[j] <= s[i])
            )
        )
    )
);

    % Redundant constraint on the lower bound of the resource capacity
    % modelling the task-decomposition of a cumulative constraint
%constraint redundant_constraint(
%/\  forall(i in Tasks, r in Res where rr[r, i] > 0)(
%        rcap[r] >= rr[r, i] + sum(j in unrelated[i] where rr[r, j] > 0)(
%            rr[r, j] * not(
%                (s[j] + dur[j] <= s[i]) \/ (s[j] > s[i])
%            )
%        )
%    )
%);

    % Resource availability constraint
    %
constraint objective = sum(r in Res)( cost[r] * rcap[r] );

    % Upper bound on the resource availability cost wrt. to the
    % earliest start time schedule
constraint objective <= sum(r in Res)( cost[r] * rusage_es[r] );

    % Upper bound on the resource availability cost wrt. to the
    % latest completion time schedule
constraint objective <= sum(r in Res)( cost[r] * rusage_ls[r] );



%-----------------------------------------------------------------------------%
% Search.

ann: search1 = seq_search([
    int_search(rcap, first_fail, indomain_min, complete),
    int_search(s, smallest, indomain_min, complete)
]);

array [Res] of Res: sort_idx_cost_desc = reverse(arg_sort(cost));
ann: search2 = seq_search([
    int_search([rcap[sort_idx_cost_desc[r]] | r in Res], input_order, indomain_min, complete),
    int_search(s, smallest, indomain_min, complete)
]);

solve
   :: search1
   minimize objective;

%-----------------------------------------------------------------------------%
% Output.

output [
    "s = \(s);\n",
    "rcap = \(rcap);\n",
    "objective = \(objective);\n"
];

%-----------------------------------------------------------------------------%

