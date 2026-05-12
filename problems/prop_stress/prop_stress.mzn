%% propagation stress
%% Problem is unsatisfiable
int: k; %% number of times round the loop
int: n; %% number of iterations of change per loop 
int: m; %% m^2 propagators per change of loop 
 
array [0..n] of var 0..k*n : y;
array [0..m] of var 0..k*n : x;

% Nondecreasing chain on y.
constraint
    forall(i in 2..n)(
        y[i-1] - y[i] <= 0 
    );

% Bounds each y[i] relative to y[0], tightening as i grows.
constraint
    forall(i in 1..n)(
        y[0] - y[i] <= n - i + 1
    );

% Link the tail of y to the head of x.
constraint
    y[n] - x[0] <= 0;


% Nondecreasing chain on x.
constraint
    forall(i in 0..m-1)(
        forall(j in i+1..m)(
            x[i] - x[j] <= 0
        )
    );

% Closing inequality creates contradiction with the chains (benchmark is UNSAT).
constraint x[m] - y[0] <= - 2;

solve :: int_search(y ++ x, input_order, indomain_min, complete)
      satisfy;
