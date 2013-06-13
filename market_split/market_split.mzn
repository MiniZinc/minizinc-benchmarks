%-----------------------------------------------------------------------------%
%
% Market split problem
%
% http://did.mat.uni-bayreuth.de/~alfred/marketsplit.html
%
% http://miplib.zib.de/
%
%-----------------------------------------------------------------------------%

int: m;
int: n;

array[1..m, 1..n+1] of int: a;

array[1..n] of var 0..1: x;

constraint
    forall(i in 1..m)(
        sum(j in 1..n)( a[i,j]*x[j] ) = a[i,n+1]
    );

solve :: int_search(x, input_order, indomain_min, complete) 
  satisfy;

output [show(x)];

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
