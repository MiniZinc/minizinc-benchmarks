%% search stress test for propagation engines
%% Unsatisfiable: should require lots of search to fail
%% Simple graph coloring problem
%%
%%       x[2]         x[k+2]                               x[(n-1)*k+2]
%%      /    \       /      \                             /            \
%%  x[1]- .. - x[k+1]- ...  - x[2k+1]  .....  x[(n-1)*k+1]-    ...     - x[nk+1] - x[1]
%%      \    /       \      /                             \            /
%%       x[k]         x[2k]                                   x[nk]
%%
%%
%% Each of x[1] .. x[i*k+1] are forced to have the same color.  But the last != is not satisfiable

int: n;  %% number of copies of graph in sequence
int: k;  %% size of each subgraph and number of colors

array[1..n*k+1] of var 1..k:x;  %% colors of each node.

predicate alldifferent_neq(array[int] of var int:y) =
	  forall(i, j in index_set(y) where i < j)(
	  	 y[i] != y[j]
          );

constraint
    forall(i in 1..n)(
    	  forall(j in 2..k)(
	  	   x[(i-1)*k+1] != x[(i-1)*k+j] /\
		   x[i*k+1] != x[(i-1)*k + j]
	  ) /\
	  alldifferent_neq([ x[(i-1)*k + j] | j in 2..k ])
    );

constraint x[1] != x[n*k+1];

solve ::
      int_search(x, first_fail, indomain_min, complete)
      satisfy;
