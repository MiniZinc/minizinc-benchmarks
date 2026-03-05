%------------------------------------------------------------------------------%
% Model for Test Scheduling Problem (CSPlib problem 073)
%
% Model by Gustav Björdal
% 17-05-2018 
%------------------------------------------------------------------------------%
% Includes

include "globals.mzn";

%------------------------------------------------------------------------------%
% Parameters

enum Machines;
enum Resources;

array [Resources] of int: capacity;

int: nTests;
set of int: Tests = 1..nTests;
array [Tests] of int: duration;
array [Tests] of set of Machines: possibleMachines;
array [Tests] of set of Resources: usedResources;

int: minMakespan = max([sum([duration[t] | t in Tests where r in usedResources[t]])    | r in Resources]);
int: maxMakespan = max([sum([duration[t] | t in Tests where m in possibleMachines[t]]) | m in Machines ]); 

%------------------------------------------------------------------------------%
% Variables

array [Tests] of var Machines: usesMachine; % which machine is each test run on
array [Tests] of var 0..maxMakespan-max(duration): startTime;

%------------------------------------------------------------------------------%
% Constraints

    % Tests can only run on valid machines
    %
constraint forall(t in Tests)(
    usesMachine[t] in possibleMachines[t]
);

    % Tests do not overlap when running on the same machine
    %
constraint forall(m in Machines)(
    cumulative(
        startTime, duration, [ bool2int(usesMachine[t] = m) | t in Tests ], 1
    )
);

    % Tests that use the same resource do not overlap in time
    %
constraint forall(r in Resources)(
    let{
        array[int] of var 0..maxMakespan-max(duration): startTimeR = 
            [startTime[t] | t in Tests where r in usedResources[t]];
        array[int] of var int: durationR = 
            [duration[t] | t in Tests where r in usedResources[t]];
    } in (
        % Currently, the capacity is 1 for all r in all instances:
        %cumulative(startTimeR, durationR, [ 1 | dummy in durationR ], capacity[r]) 
        disjunctive(startTimeR, durationR) 
    )
);

%------------------------------------------------------------------------------%
% Symmetry breaking constraint

% Some Tests can only run on a proper subset of the available machines.
% The machines in the union of those subsets are not nessesarily symmetrical, but the other ones are.

set of Machines: nonSymmetricalMachines = 
    { m | t in Tests, m in possibleMachines[t] where card(possibleMachines[t]) < card(Machines)};
set of Machines: symmetricalMachines = Machines diff nonSymmetricalMachines;

constraint symmetry_breaking_constraint(
    if card(index_set(symmetricalMachines)) > 0 then
        value_precede_chain(symmetricalMachines, usesMachine)
    else
        true
    endif
);
% Submitted version of the symmetry breaking constraint
%constraint if card(index_set(symmetricalMachines)) > 0 then 
%    symmetry_breaking_constraint(value_precede_chain(symmetricalMachines, usesMachine))
%  else true endif;

%------------------------------------------------------------------------------%
% Objective

var minMakespan..maxMakespan: objective; % makespan

constraint objective = max([startTime[t] + duration[t] | t in Tests]);
constraint redundant_constraint(min(startTime) = 0);

%------------------------------------------------------------------------------%
solve
    :: seq_search([
        int_search(
            [startTime[t] | t in Tests where card(usedResources[t]) > 0], 
            first_fail, indomain_min, complete
        ),
        int_search(
            [if i = 1 then startTime[t] else usesMachine[t] endif 
            | t in reverse(arg_sort(duration)), i in 1..2],
            input_order, indomain_min, complete )
    ])
    minimize objective;

%------------------------------------------------------------------------------%

output [
    "usesMachine = \(usesMachine);\n",
    "startTime = \(startTime);\n",
    "objective = \(objective);\n"
];
