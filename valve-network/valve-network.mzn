%
% Valve network planning for Advent of Code 2022 Day 16.
%
% From https://github.com/zayenz/advent-of-code-2022
% Instead of using differnet networks for varying hardness, this model 
% uses different planning horizons for adjusting the hardness of the problem.
%
% Model by Mikael Zayenz Lagerkvist
%

include "globals.mzn";

% Input
enum Nodes;
Nodes: first_node;

array[Nodes] of int: flow;
array[Nodes] of set of Nodes: connections;

int: horizon;

set of int: Minutes = 1..horizon;
set of int: Steps = Minutes diff {1};

% Data

enum Action = {Move, Open};
enum Person = {Me, Elephant};
function Person: other(Person: person) = 
    if person = Me then Elephant else Me endif;

% Variables
array[Nodes, Minutes] of var bool: open;
array[Minutes, Person] of var Nodes: position;
array[Steps, Person] of var Action: action;

array[Minutes] of var int: current_flow = array1d(Minutes, [
    sum(node in Nodes) (
        open[node, minute] * flow[node]
    )
  | minute in Minutes
]);


% Constraints

% Initial state
constraint position[1, Me] = first_node /\
    position[1, Elephant] = first_node /\
    forall (node in Nodes) (
      open[node, 1] = false
    );

% Steps
constraint forall (step in Steps, person in Person) (
    if action[step, person] = Open then
        open[position[step, person], step] = true /\
        forall (node in Nodes where 
                  (node != position[step, Me] /\ 
                  node != position[step, Elephant])) (
            open[node, step] = open[node, step-1]
        ) /\
        position[step, person] = position[step-1, person]
    else
        forall (node in Nodes where node != position[step, other(person)]) (
          open[node, step] = open[node, step-1] 
        ) /\
        position[step, person] in connections[position[step-1, person]]
    endif 
) /\
    forall (step in Steps, node in Nodes) (
        if (action[step, Me] = Open /\ position[step, Me] = node) \/ 
           (action[step, Elephant] = Open /\ position[step, Elephant] = node)
        then
            open[node, step] = true        
        else
            open[node, step] = open[node, step-1]            
        endif
);

var int: checksum = sum(current_flow);



% Solve and output
solve :: int_search([ 
    [action[s, p], position[s, p]][i] 
  | s in Steps, p in Person, i in 1..2
], input_order, indomain_max)
maximize checksum;

output 
[
  "Minute \(m): Position me=\(position[m, Me]), elephant=\(position[m, Elephant]), Open valves: \({n | n in Nodes where open[n, m]})\n"
  | m in Minutes
] ++
[
  "checksum: ", show(checksum), "\n",
];

%
% Definition of network.
%
% This is one possible input for the problem in https://adventofcode.com/2022/day/16
%
% Multiple networks are possible to vary hardness, but planning length is used instead 
% for simplicity. Normally the below would be in a dzn file instead.
%

Nodes = { GJ, HE, ET, SG, LC, EE, AA, TF, GO, QE, MI, BR, UV, EH, WK, NT, KI, AH, EL, GP, GM, LU, LB, QC, JJ, MM, VI, NV, VT, RE, FO, DV, SQ, OQ, FF, IV, HY, ML, JS, KU, QA, EU, SV, JG, DW, UD, QJ, HU, ZR, YA, JH, OS, LG, SB, UU, VL, AO, EM};
first_node = AA;

flow = [14, 0, 0, 0, 0, 13, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 9, 0, 0, 0, 0, 18, 0, 0, 0, 0, 10, 12, 23, 3, 0, 8, 0, 0, 5, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 15, 0, 4, 0, 0, 0, 0];

connections = [
{UV, AO, MM, UD, GM},
{QE, SV},
{LU, SB},
{FF, SB},
{QJ, GM},
{RE, BR},
{QC, ZR, NT, JG, FO},
{LU, MM},
{LB, AH},
{LG, HE},
{KU, FF},
{HY, EE},
{GP, GJ},
{UU, FF},
{HY, EL},
{FF, AA},
{OQ, AO},
{GO, RE},
{WK, SQ},
{SB, UV},
{LC, GJ},
{UU, DW, TF, ET, ML},
{GO, VI},
{ML, AA},
{QJ, DV},
{TF, GJ},
{LB},
{SB, KU},
{HY, JG},
{AH, EE},
{SB, AA},
{JH, UD, JJ},
{EL, QA},
{KI, IV, JS},
{EU, NT, SG, MI, EH},
{LG, OQ},
{VT, BR, WK},
{LU, QC},
{EM, OQ},
{MI, VL, NV, HU, DW},
{OS, SQ},
{FF, OS},
{QJ, HE},
{AA, VT},
{LU, KU},
{DV, GJ},
{JJ, SV, LC, EM, YA},
{JH, KU},
{AA, VL},
{QJ, OS},
{HU, DV},
{EU, YA, QA},
{QE, IV},
{FO, SG, NV, GP, ET},
{EH, LU},
{ZR, KU},
{GJ, KI},
{QJ, JS}
];
