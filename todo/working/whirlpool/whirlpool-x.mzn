% perfect diagonal extended whirlpool permutation
%
% a whirlpool permutation is an n x m matrix containing number 1.. n*m where every 2 x 2 sub matrix is either ordered clockwise or counter clockwise
% an extended whirlpool permutation requires that the outside ring is ordered cw or ccw, and the ring inside that, etc
% a perfect diagonal whirlpool permutation required n = m and that the sum of both diagonals is n*(n+1)*(n+1) div 2 (i.e. the sum for a perfect square of the same size)


int: n;
int: m = n;
set of int: ROW = 1..m;
set of int: COL = 1..n;
array[ROW,COL] of var 1..m*n: x;

include "alldifferent.mzn";
constraint alldifferent(x);

      
predicate whirlpool(array[int] of var int: x) = 
          let {int: n = length(x); } in
          sum(i in 1..n)(x[i] < x[i mod n + 1]) in { 1, n-1 }; 
                                     

constraint forall(i in 1..m-1, j in 1..n-1)
%                 (whirlpool(x[i,j], x[i,j+1], x[i+1,j+1], x[i+1,j])); 
                 (whirlpool([x[i,j], x[i,j+1], x[i+1,j+1], x[i+1,j]])); 
             
constraint forall(k in 0..min(n,m) div 2-1)
                 (whirlpool(    [ x[i,j] | i in {k+1}, j in 1+k..m-k] ++ [ x[i,j] | j in {m-k}, i in k+2..n-k ] 
                             ++ [ x[i,m+1-j] | i in {n-k}, j in k+2..m-k ] ++ [ x[n+1-i,j] | j in { k+1 }, i in k+2..n-k-1 ]));
                                                      
                                             
constraint sum(i in 1..n)(x[i,i]) = n*(n+1)*(n+1) div 2;                                              
constraint sum(i in 1..n)(x[i,n+1-i]) = n*(n+1)*(n+1) div 2;                                              
                                               
                                                 
% output [show2d(x)];
output ["x = array2d(\(ROW), \(COL), \(x));\n"];

solve :: int_search(array1d(x), first_fail, indomain_min) satisfy;