% Steiner systems model
%
% Written by Jason Nguyen
% MIT Licence
%
% Copyright 2021 Monash University
% 
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to
% deal in the Software without restriction, including without limitation the
% rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
% sell copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
% 
% The above copyright notice and this permission notice shall be included in
% all copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.

% A Steiner system S(t, k, N) is a set X of cardinality N and a collection C
% of subsets of X of cardinality k (called ‘blocks’), such that any t elements
% of X are in exactly one block. Any Steiner system must have exactly
% m = (N choose t) / (k choose t) blocks.

int: t;
int: k;
int: N;

function int: nCr(int: n, int: r) = product (n-r+1..n) div product(1..r);

set of int: X = 1..N;
int: m :: add_to_output = nCr(N, t) div nCr(k, t);

array [1..m] of var set of X: C :: add_to_output;

constraint forall (i in 1..m) (card(C[i]) = k);
constraint forall (i in 1..m-1, j in i+1..m) (card(C[i] intersect C[j]) <= t - 1);

constraint symmetry_breaking_constraint(
  forall (i in 1..m-1) (C[i] < C[i + 1])
);

bool: nosets_set_search = show(set_search([{}], input_order, indomain_min, complete)) = "seq_search([bool_search(set2bools(xx[i]),a1,a2,a3) | i in index_set(xx), ])";
solve :: set_search(C, input_order, if nosets_set_search then indomain_max else indomain_min endif, complete) satisfy;
