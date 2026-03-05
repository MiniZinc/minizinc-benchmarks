% cuttingstock with stack limits
int: n; % number of products
set of int: PROD = 1..n;
array[PROD] of int: size;
array[PROD] of int: number;
int: sl; % open stack limit;
int: s; % size of stock piece
int: maxn = max(number);
int: k; % maximum cuts;
set of int: CUT = 1..k;

array[CUT,PROD] of var 0..s: x; % number of pieces of PROD p on cutting stock piece c
array[CUT] of var 0..maxn: m;   % number of copies of cutting stock piece c
array[CUT] of var 0..1: used;   % did we use the cut
var 0..k: patterns = sum(used);

array[PROD] of var CUT: first = [ min(c in CUT)(c + n*(1 - (x[c,p] > 0))) | p in PROD];
array[PROD] of var CUT: last = [ max(c in CUT)((x[c,p] > 0)*c)  | p in PROD];
array[PROD] of var 0..n: dur = [ last[p] - first[p] | p in PROD];

% We must cut enough of each product
constraint forall(p in PROD)(sum(c in CUT)(x[c,p]*m[c]) >= number[p]);

% Each cut must only fit on the stock piece
constraint forall(c in CUT)(sum(p in PROD)(x[c,p] * size[p]) <= s);

% Maximum stacks open
include "cumulative.mzn";
constraint cumulative(first, dur, [1 | p in PROD], sl); 

% Minimize wastage
var 0..maxn*k: objective; 

constraint objective = sum(m);


solve 
    :: seq_search([
        int_search([ if j = 0 then x[c,p] elseif p = n then m[c] else 0 endif 
                   | c in CUT, p in PROD, j in 0..1 ], input_order, indomain_min, complete),
        int_search( used, input_order, indomain_min, complete)
    ])
    minimize objective;

% symmetry elimination: unused cuts are at the beginning
constraint symmetry_breaking_constraint(forall(c in CUT, p in PROD)(x[c,p] <= used[c]*s));
constraint symmetry_breaking_constraint(forall(c in CUT)(m[c] <= used[c]*maxn));
constraint symmetry_breaking_constraint(forall(c in CUT)(used[c] <= m[c]));
constraint symmetry_breaking_constraint(forall(c in 1..k-1)(used[c] <= used[c+1])); 

output [
    "x = array2d(\(CUT), \(PROD), \(x));\n",
    "m = array1d(\(CUT), \(m));\n",
    "used = \(used);\n",
    "objective = \(objective);\n"
];
