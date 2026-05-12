int: n;
array [0..n] of var 0..10*n : y;
array [0..n] of var 0..10*n : x;

% Monotone chain on y[1..n].
constraint
    forall(i in 2..n)(
        y[i-1] - y[i] <= 0 
    );

% Each y[i] must stay close enough to y[0]; tighter as i increases.
constraint
    forall(i in 1..n)(
        y[0] - y[i] <= n - i + 1
    );

% Link both chains through y[n] and x[0].
constraint
    y[n] - x[0] <= 0;


% Monotone chain on x[1..n].
constraint
    forall(i in 1..n-1)(
        forall(j in i+1..n)(
            x[i] - x[j] <= 0
        )
    );

constraint y[0] >= n;

solve satisfy;

output [ "x = array1d(0..", show(n), ", ", show(x), ");\n",
         "y = array1d(0..", show(n), ", ", show(y), ");\n"
];
