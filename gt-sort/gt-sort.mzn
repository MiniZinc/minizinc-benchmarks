% Modifications by MiniZinc Challenge Organizers:
% - Add search annotation and refactor out y variables so that they can be searched
% - Name objective variable `objective`
% - Move c into data rather rather than using uniform random

include "globals.mzn";

enum Run = { BASELINE, BEST, WORST};

Run: run::output;

% BASELINE = false;

% 2*x1 + 3*x2 + 2*x3 + 5*x4 <= k
array[int] of int: c::output;

% c = [2,3,2,5]; % same as baseline

% c = [1,3,3,5]; % better by 1
% f = 0.75;

% generate instance of n variables with coefficients [1,ub]
int: n::output;
int: ub::output;
float: f::output; % k is chosen based on strictness factor f

% c = [ uniform(1,ub) | i in 1..n ] ++ if n mod 2 == 1 then [0] endif; % pad with 0 term if odd
array[int] of set of int: s = [ {0, ci} | ci in reverse(sort(c)) ];

int: u::output = sum([ max(si) | si in s]);
int: k::output = round(f * u);

% number of layers
set of int: L = 1..(1+ceil(log2(length(c))));

% x[i,j] = values of node j at layer i
array[L,index_set(s)] of var set of min(si in s, a in si)(a)..k: x;

constraint x[1,..] = s; % first layer is fixed (! sometimes causes a bug with nosets.mzn for chuffed)

any: y_pairs = [
  let {
    int: pairs = ceil(length(c) / (2^i));
    array[1..pairs,1..2] of var 1..(2*pairs): y;
  } in (pairs: pairs, y: y)
| i in L diff {max(L)}];
any: y_vars :: output = [y_j | z_i in y_pairs, y_j in z_i.y];

constraint forall(i in L diff {max(L)})( % for layer i, constrain parents in layer i+1
  let {
    int: pairs = y_pairs[i].pairs;
    int: next_pow2 = 2^(pairs-1);

    % y[j,1] is the index of the left child of parent node (i+1,j)
    any: y = y_pairs[i].y;
    constraint alldifferent(y);
    constraint strictly_increasing(j in 1..pairs)(y[j,1]); % symmetry
    constraint if run = BASELINE then y = array2d(1..pairs, 1..2, [ z | z in 1..(pairs*2) ]) endif ;
  } in
  forall(j in index_set(s))(
  if j <= pairs then % pair j
    let {
      var int: ja = y[j,1];
      var int: jb = y[j,2];
      constraint ja < jb; % symmetry

      var set of int: a = x[i,ja];
      var set of int: b = x[i,jb];
    } in
      % parent contains the all possible sums of child nodes
    (x[i+1,j] = { (ai in a) * (bi in b) * (ai + bi) | ai in ub(a), bi in ub(b) where ai+bi <= k })
    % alternative which performs way worse: (x[i+1,j] = { min(ai + bi, k+1) | ai in a, bi in b })
  elseif j <= next_pow2 then % handle layer with odd number of nodes by padding
    x[i+1,j] = {0}
  else % unused nodes are fixed to empty
    x[i+1,j] = {}
  endif
));

% minimize sum of values in all nodes (includes first layer)
% TODO don't count the 0's in the sets
var int: obj ::output =  sum(xi in x)(card(xi));
var int: objective = if run = WORST then -obj else obj endif;
solve :: seq_search([
  set_search(x, input_order, indomain_min),
  int_search(y_vars, smallest, indomain_min)
]) minimize objective;
