
int: n; %% number of rows
int: m; %% number of columns

var int: cost;
array[0..n+1,0..m+1] of var 0..1: a; %% whether i,j is alive

array[1..n, 1..m] of var 0..9: s; %% sum of the 8 squares around i,j



constraint
    forall(i in 1..n, j in 1..m)(
    	     s[i,j] = a[i-1,j-1] + a[i-1,j] + a[i-1,j+1]
	            + a[i,j-1]              + a[i,j+1]
		    + a[i+1,j-1] + a[i+1,j] + a[i+1,j+1] /\
	     ((a[i,j] == 1) <-> (2 <= s[i,j] /\ s[i,j] <= 3))
    );
constraint cost = sum(i in 1..n, j in 1..m)(a[i,j]);

solve :: int_search([ a[i,j] | i in 1..n, j in 1..m ], input_order, indomain_max, complete)
      maximize cost;


output ["cost = ", show(cost), 
        ";\na = [|\n"] ++
	[ show(a[i,j]) ++  
          if j == m then if i == n then "|];\n" else "|\n" endif
	            else "," endif |
	  	       i in 1..n, j in 1..m ]++
	[ "\n\n%     " ] ++
	[ (if fix(a[i,j]) = 1 then "X" else " " endif) ++ if j == m then "\n%     " else "" endif | 
         i in 1..n, j in 1..m ];
    
