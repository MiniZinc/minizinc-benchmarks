% new zinc file GridColoring.mzn


int: n; % width of grid
int: m; % height of grid
% variables 
array[1..n,1..m] of var 1..min(n,m):x;
var 1..min(n,m): objective; % number of colours used

% model
constraint forall(i in 1..n, k in 1..m)(x[i,k] <= objective);
constraint forall(i in 1..n, j in i+1..n, k in 1..m, l in k+1..m)(
				x[i,k] != x[i,l] \/ x[i,l] != x[j,l] \/ x[j,k] != x[j,l] \/ x[i,k] != x[j,k]
		 	);
		 	
solve :: int_search([x[i,k] | i in 1..n, k in 1..m], first_fail, indomain_min, complete)
	  minimize objective;		 	 

% data
output [ show(x[i,k]) ++ if k == m then "\n" else " " endif |
		 i in 1..n, k in 1 ..m ] ++ 
	["objective = ", show(objective), "\n"];
		 
