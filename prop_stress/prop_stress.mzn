%% propagation stress
%% Problem is unsatisfiable
int: k; %% number of times round the loop
int: n; %% number of iterations of change per loop 
int: m; %% m^2 propagators per change of loop 
 
array [0..n] of var 0..k*n : y;
array [0..m] of var 0..k*n : x;

constraint
    forall(i in 2..n)(
        y[i-1] - y[i] <= 0 
    );

constraint
    forall(i in 1..n)(
        y[0] - y[i] <= n - i + 1
    );

constraint
    y[n] - x[0] <= 0;


constraint
    forall(i in 0..m-1)(
        forall(j in i+1..m)(
            x[i] - x[j] <= 0
        )
    );

constraint x[m] - y[0] <= - 2;


solve :: int_search(y ++ x, input_order, indomain_min, complete)
      satisfy;

output [ "x = array1d(0..", show(m), ", ", show(x), ");\n",
         "y = array1d(0..", show(n), ", ", show(y), ");\n"
];


