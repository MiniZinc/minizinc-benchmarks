/* 
  Sudoku solver in MiniZinc.

  The following 91 problems are from the Gecode Sudoku model:
  http://www.gecode.org/gecode-doc-latest/sudoku_8cpp-source.html

  All the 91 instances are available as:
  http://www.hakank.org/minizinc/sudoku_problems2/sudoku_p0.dzn
  ...
  http://www.hakank.org/minizinc/sudoku_problems2/sudoku_p90.dzn

  This model is a fixed search model. 

  This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
  See also my MiniZinc page: http://www.hakank.org/minizinc

*/

% Licensed under the MIT license (https://opensource.org/licenses/MIT)

% Changes by the MiniZinc Organisers:
% - Modify the search strategy to not use dom_w_deg, which is not allowed in
%   the Challenge.

include "globals.mzn"; 


int: n;
int: reg = ceil(sqrt(int2float(n))); % size of the regions
array[1..n, 1..n] of var 1..n: x;

array[1..n, 1..n] of opt int: board;
constraint forall (i, j in 1..n) (x[i, j] ~= board[i, j]);

% solve :: int_search(array1d(x), dom_w_deg, indomain_split) satisfy;        
solve :: int_search(array1d(x), first_fail, indomain_split) satisfy;        

%
% All rows, columns, and regions contains different numbers.
%
constraint 
  % rows and columns
  forall(i in 1..n) (
     alldifferent([x[i,j] | j in 1..n]) /\
     alldifferent([x[j,i] | j in 1..n]) 
  )
  /\ % regions
  forall(i in 0..reg-1,j in 0..reg-1) (
    alldifferent([x[r,c] | r in i*reg+1..i*reg+reg, c in j*reg+1..j*reg+reg]) 
  )
;

output 
[
  if j = 1 then "\n" else " " endif ++
    show(x[i,j])
  | i,j in 1..n
] ++ ["\n"];
