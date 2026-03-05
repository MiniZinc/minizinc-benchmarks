% monduko model
% Description in https://www.reddit.com/r/generative/comments/1fxp5ng/irregular_mondoku_art/
%
% For each row and column in a matrix, each color is represented but only in one group.
% That is, for width 4 and 2 colors, RRGG is allowed, but not RGGR.
%
% In order to Get a "balanced" output, this model minimizes the maximum difference 
% between the minimum and maximum occurences of any color for any row or column.
% That is, for a row GGGBBRRRR, there are four R's and two B's, which gives a difference
% of 2.
%


% By Mikael Zayenz Lagerkvist 2024
% Released under MIT license


% Modifications by MiniZinc Challenge Organizers:
% - Add search annotation

include "globals.mzn";

%
% Data definitions, the width, height, and number of colors
%

int: W; % width
int: H; % height
int: C; % num colors

%
% Derived data, sets of ints
%

set of int: Colors = 1..C;
set of int: Width  = 1..W;
set of int: Height = 1..H;

%
% Variables
%

array[Width, Height] of var Colors: puzzle;

% Derived variables, has the value at the start of a group only, other values are 0
% First is for groups across the board
array[Width, Height] of var {0} union Colors: across = array2d(Width, Height, [ 
    if puzzle[w-1,h] default 0 != puzzle[w,h] then
        puzzle[w, h]
    else
        0
    endif | w in Width, h in Height]);
% Swcond is for groups down the board
array[Width, Height] of var {0} union Colors: down = array2d(Width, Height, [ 
    if puzzle[w,h-1] default 0 != puzzle[w,h] then
        puzzle[w, h]
    else
        0
    endif | w in Width, h in Height]);


%
% Constraints, count the number of groups across and down using
% the global cardinality constraint
%

% For all the rows, each row must contain one group of each color
constraint forall(h in Height) (
    global_cardinality(across[.., h], 
                       set2array({0} union Colors), 
                       [W - C] ++ [1 | c in Colors]
    )
);

% For all the columns, each row must contain one group of each color
constraint forall(w in Width) (
    global_cardinality(down[w, ..], 
                       set2array({0} union Colors), 
                       [H - C] ++ [1 | c in Colors]
    )
);


%
% Optimization variables
%

% For each row, the difference between the max and min number of occurences for all colors
array[int] of var int: diff_across = [
    let {
        array[int] of var int: occurences = global_cardinality(puzzle[.., h], set2array(Colors));
        var int: minimum = min(occurences);
        var int: maximum = max(occurences);
    } in
    maximum - minimum
  | h in Height];

% For each column, the difference between the max and min number of occurences for all colors
array[int] of var int: diff_down = [
    let {
        array[int] of var int: occurences = global_cardinality(puzzle[w, ..], set2array(Colors));
        var int: minimum = min(occurences);
        var int: maximum = max(occurences);
    } in
    maximum - minimum
  | w in Width];
  
  
% Symmetry breaking, the colors are interchangable
constraint symmetry_breaking_constraint(value_precede_chain(Colors, array1d(puzzle)));


% Objective is to minimize the maximum difference for any row or column, as one way to keep it all balanced
var int: objective = max(diff_across ++ diff_down);

%
% Solve using default heuristics and output
%

solve :: int_search(puzzle, first_fail, indomain_min) minimize objective;
