%------------------------------------------------------------------------------
% Generalized Peaceable Queens
%
% Model by Hendrik 'Henk' Bierlee
%
% On a n-by-n chessboard, for q colors/armies of queens (black queens, white
% queens, purple queens, etc.), maximize the number of queens on the board such
% that queens from different armies do not attack each other. The sizes of the
% armies must be equal.
%
% All known optimal solutions for q=2 case are on https://oeis.org/A250000
% Some insight for this model is due to Smith et. al, CP'2004
%------------------------------------------------------------------------------
% Copyright 2022 Hendrik Bierlee
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.
%------------------------------------------------------------------------------

include "all_equal.mzn";
include "global_cardinality.mzn";
include "lex_lesseq.mzn";
include "regular.mzn";
include "value_precede_chain.mzn";

int: n;  % board dimensions
int: q;  % number of armies

enum Armies = Army(1..q);  % black army, white army, purple army, etc.
enum Squares = {EMPTY} ++ Q(Armies);

array[1..n,1..n] of var Squares: x; % x[i,j] designates for square i,j whether it is empty, or occupied by a queen of a particular army

% A regular constraint allowing a set (row, column or diagonal) of squares to only have queens of the same army, or empty squares
predicate at_peace(array[int] of var int: x) = 
  regular(
    x,
    card(Squares), % number of states
    card(Squares), % number of inputs
    d, % d = (input,states) -> status union {0}
    EMPTY, % starting state: empty
    1..max(d), % accepting states: all except 0
  );

array[Squares,Squares] of int: d = array2d(Squares,Squares,
  Squares ++ % EMPTY,Armies[1],Armies[2], ...
  % Armies[row] (stay in state if encounter empty), 0 (fail if encounter other army), 0, .., Armies[row] (stay in state if encounter same army), 0, 0, ..
  [ if col in {EMPTY,row} then row else 0 endif | row in Squares diff {EMPTY}, col in Squares ]);

% Example DFA transition function for q=2:
  %[|    EMPTY,Armies[1],Armies[2]|
  %  Armies[1],Armies[1],        0|
  %  Armies[2],        0,Armies[2]|];

% rows and columns
constraint forall(i in 1..n)(
  at_peace(x[i,..]) /\ at_peace(x[..,i])
);

% diagonals in one direction (except corners)
constraint forall(k in -n+2..n-2)(
  at_peace([ x[i,j] | i,j in 1..n where i+j-n-1 == k ])
    % .ab
    % abc
    % bc.
);

% diagonals in the other direction (except corners)
constraint forall(k in -n+2..n-2)(
  at_peace([ x[i,j] | i,j in 1..n where i-j == k ])
  % ba.
  % cba
  % .cb
);

% count the number of queens in each army
array[Squares diff {EMPTY}] of var 0..(n*n) div q: counts;
constraint global_cardinality(x, array1d(Squares diff {EMPTY}, Squares diff {EMPTY}), counts);
constraint all_equal(counts[Squares diff {EMPTY}]); % all armies must be of equal size

% maximize the size of the armies
var int: objective = counts[Q(Armies[1])];
solve :: int_search(x, input_order, indomain_min) maximize objective;

% Symmetry: every solution can be rotated and/or reflected
constraint symmetry_breaking_constraint(var_sqr_sym(x));

% Symmetry: we can exchange one queens in one army for another
constraint symmetry_breaking_constraint(value_precede_chain(Squares diff {EMPTY}, array1d(x)));

array[int] of string: ALPHABET = [ "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z" ];

output [
  if fix(x[i,j]) = EMPTY then "." elseif q <= length(ALPHABET) then ALPHABET[fix(x[i,j])-1] else show(Q^-1(fix(x[i,j]))) endif
  ++ if j == n then "\n" else "" endif
    | i,j in 1..n] ++
  ["n = \(n);\nq = \(q);\ncounts = \(counts);\nobjective = \(objective);\n"]
    ;

predicate var_sqr_sym(array[int,int] of var int: x) =
  let { int: n = card(index_set_1of2(x));
        int: n2 = card(index_set_2of2(x));
        constraint assert(n = n2,"square symmetry applied to non-square array");
        int: l = n * n;
        array[1..l] of var int:
          y = [ x[i,j] | i in index_set_1of2(x),
                         j in index_set_2of2(x) ];
        array[1..8,1..l] of 1..l:
          p = array2d(1..8,1..l,
            [ if k == 1 then i*n + j - n 
              elseif k == 2 then (n - j)*n + i           % r270
              elseif k == 3 then (n - i)*n + (n - j)+1   % r180
              elseif k == 4 then (j*n - n) + (n - i + 1) % r90
              elseif k == 5 then (n - i)*n + j           % x flip
              elseif k == 6 then (i*n - n) + (n - j + 1) % y flip
              elseif k == 7 then (n - j)*n + (n - i + 1) % d2 flip
              else               (j*n - n) + i           % d1 flip
              endif
            | k in 1..8, i,j in 1..n]) }
  in var_perm_sym(y,p);

predicate var_perm_sym(array[int] of var int: x,
                       array[int,int] of int: p) =
  let { int: l = min(index_set_1of2(p)),
        int: u = max(index_set_1of2(p)),
	array[1..length(x)] of var int:
          y = [ x[i] | i in index_set(x) ] }
  in
  forall (i, j in l..u where i != j) (
    var_perm_sym_pairwise(y,
      [ p[i,k] | k in index_set_2of2(p) ],
      [ p[j,k] | k in index_set_2of2(p) ])
  );

predicate var_perm_sym_pairwise(
    array[int] of var int: x,
    array[int] of int: p1,
    array[int] of int: p2) =
  let { int: n = length(x),
        array[1..n] of 1..n:
          invp1 = [ j | i, j in 1..n
                      where p1[j] = i ] }
  in
  lex_lesseq(x, [ x[p2[invp1[i]]] | i in 1..n ]);


