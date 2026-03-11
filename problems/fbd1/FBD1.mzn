%Copyright 2025 Andrew Gill
%Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
%The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
%THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

% Modifications by MiniZinc Challenge Organizers:
% - Add search annotation
% - Name objective variable `objective`

% FBD1 design construction.
% Global constraints.
include "globals.mzn";

% Set up parameters. The number of factors is k, which represents the size of the design problem.
% For k in 2..8 and using 1 thread, optimal solutions are easy-to-solve, and are found within 10 minutes (using Gecode).
% Toy instances are represented by k=2 or k=3.
% Using 30 threads, k=9 takes 13 minutes to solve (using Gecode). With 1 thread, it takes 2.25 hours.
% Thus, hard-to-solve instances will be k in 10..20.

int: k; % Read in from FBDxx.dzn
int: maxn = 5+k^3; % Upper bound for the design size and by inference the design variables.

% The design/decision variables.
set of int: main_factors = 1..k;
array[main_factors] of var 1..maxn div 2 : n;
var 1..maxn+1: n_star;

% The intermediate variables.
array[int] of var int: Q ::output = [2*ni | ni in n];
array[int] of var int: T_plus ::output = [n[j] + n[i] | i,j in main_factors where i < j];
array[int] of var int: T_minus ::output = [n[j] - n[i] | i,j in main_factors where i < j];
array[int] of var int: Q_folded ::output = [2*n[k] + n_star - 2*ni | ni in n];
array[int] of var int: T_plus_folded ::output = [2*n[k] + n_star - t | t in T_plus];

% The design size (objective function).
var int: N ::output = 2*n[k] + n_star;

% Design variables strictly increasing.
constraint forall([n[i] < n[i+1] | i in main_factors where i < k]);

% Ensure all indicator frequencies are unique.
any: all_elements = n ++ T_minus ++ T_plus ++ Q ++ T_plus_folded ++ Q_folded;
constraint alldifferent(all_elements);

% Upper bound constraints.
constraint n_star <= 2*n[k] + 1;

% Lower bound constraints.
constraint forall([n[i] >= i | i in main_factors]);
constraint forall([Q[i] >= 2*i | i in main_factors]);

% Constraints from sequential approach.
constraint forall([n[j] != Q[i] | i,j in main_factors where i < j]);
constraint forall([n[j] != 3*n[i] | i,j in main_factors where i < j]);

% Find an optimal design.
var int: objective = N;
solve :: int_search(n ++ [n_star], smallest, indomain_min) minimize objective;
