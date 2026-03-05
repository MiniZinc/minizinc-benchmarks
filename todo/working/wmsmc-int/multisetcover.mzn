%
% This is a model for a weighted multi-set cover.
%
% The model and the instances are extracted from an 
% industrial use-case.
%
% Model by Mikael Zayenz Lagerkvist, 2021
%
% Licensed under the MIT license (https://opensource.org/licenses/MIT)
%
% Modified by the MiniZinc Challenge Organisers
% - Remove unused variable
% - Add search annotation
% - Call objective variable 'objective'


%
% Data definitions
%

% The number of elements
int: elements;
% The set of elements
set of int: Elements = 1..elements;

% The goal requirements
array[Elements] of int: requirements;

% The maximum requirement fo an element is also the maximum 
% number of times a candidate can be used
int: maxreq = max(requirements);

% The number of candidate sets
int: candidates;
% The set of candidate sets
set of int: Candidates = 1..candidates;

% The candidate sets
array[Candidates, Elements] of int: candidate_sets;
constraint assert(
    forall(c in Candidates, e in Elements) (candidate_sets[c, e] >= 0),
    "Candidate set counts must be positive",
    true
);

% The candidate costs
array[Candidates] of int: candidate_weights;
constraint assert(
    forall(c in Candidates) (candidate_weights[c] > 0),
    "Weights must be positive",
    true
);


%
% Variable definitions
%

array[Candidates] of var 0..maxreq: candidate_copies;

var int: objective;

% var int: used_set_count;

%
% Constraints
%

% A cover is needed
constraint forall(e in Elements) (
    requirements[e] <= sum(c in Candidates) (
            candidate_sets[c, e] * candidate_copies[c]
    )
);

% Cost is sum of candidates used
constraint objective = sum(c in Candidates) (candidate_weights[c] * candidate_copies[c]);

% The number of sets used in the cover (addded for understanding the output)
% constraint used_set_count = sum(candidate_copies);

%
% The problem is a minimization problem
%

solve :: int_search(candidate_copies, input_order, indomain_min, complete) minimize objective;