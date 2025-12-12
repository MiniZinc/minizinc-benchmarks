%------------------------------------------------------------------------------%
% Constrained Community Detection Problem
%
% The problem is to find communities in the graph with maximum modularity value 
% satisfying must-link and cannot-link constraints which indicate whether a 
% pair of vertices must assign to same or different communities.
%
% Adapted from original community-detection problem used in 2017.
%------------------------------------------------------------------------------%
% Includes

include "globals.mzn";

%------------------------------------------------------------------------------%
% Input and Derived Parameters

array [int, int] of int: A; % Adjacency matrix
set of int: NODE = assert(
    index_set_1of2(A) = index_set_2of2(A),
    "Invalid adjacency matrix",
    index_set_1of2(A)
);
int: N = card(NODE);

int: max_communities; % Max number of communities
set of int: COMMUNITY = 1..max_communities;

% Pairs of nodes which must be in the same community
array [int, 1..2] of int: same_community;
set of int: SAME = index_set_1of2(same_community);

% Pairs of nodes which must not be in the same community
array [int, 1..2] of int: diff_community;
set of int: DIFF = index_set_1of2(diff_community);

int: l = sum (array1d(A)); % Number of stubs
array [NODE] of int: k = [sum (j in NODE) (A[i, j]) | i in NODE]; % Node degrees

% Modularity matrix (multiplied by l so no fractions)
array [NODE, NODE] of int: B = array2d(NODE, NODE, [l * A[i, j] - k[i] * k[j] | i, j in NODE]);

% Objective bounds (compiler should be able to tighten using same/diff_community)
int: obj_lb = sum (i, j in NODE where i < j /\ B[i, j] < 0) (B[i, j]);
int: obj_ub = sum (i, j in NODE where i < j /\ B[i, j] > 0) (B[i, j]);

%------------------------------------------------------------------------------%
% Variables

array [NODE] of var COMMUNITY: x :: add_to_output;

var obj_lb..obj_ub: objective = sum (i, j in NODE where i < j /\ x[i] = x[j]) (B[i, j]);

%------------------------------------------------------------------------------%
% Constraints

constraint symmetry_breaking_constraint(seq_precede_chain(x));

constraint forall (s in SAME) (x[same_community[s, 1]]  = x[same_community[s, 2]]);
constraint forall (d in DIFF) (x[diff_community[d, 1]] != x[diff_community[d, 2]]);

constraint global_cardinality_low_up(
    x, 
    [c | c in COMMUNITY],
    [0 | c in COMMUNITY],
    [N | c in COMMUNITY]
);

%------------------------------------------------------------------------------%
% Solve item and search

solve :: int_search(x, input_order, indomain_min, complete) maximize objective;

% Use to output actual modularity value
% float: modularity :: output_only :: add_to_output = (2 * fix(objective) + sum (i in NODE) (B[i, i])) / l / l;
