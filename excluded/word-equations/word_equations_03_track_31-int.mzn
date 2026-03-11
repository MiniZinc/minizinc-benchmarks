%%% Original model %%%
% var string: J;
% var string: I;
% var string: K;
% var string: R;
% var string: G;
% var string: L;
% var string: N;
% var string: M;
% var string: P;
% constraint
%   ((J) ++ ("aa") ++ (J) ++ ("ab") ++ (N) ++ (L) ++ ("a") ++ (K) ++ ("b") ++ (P) ++ (P) ++ ("ba"))
%     =
%     (("a") ++ (G) ++ (I) ++ ("aa") ++ (M) ++ (M) ++ (M) ++ (M) ++ ("baaaab") ++ (R) ++ (R) ++ ("baa"));
% solve satisfy;

int: MAX_STR_LEN;
set of int: IDX_SET = 1..MAX_STR_LEN;
enum ALPHABET = {'eps', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k'};

predicate 
str_var(array[IDX_SET] of var ALPHABET: x) = 
  forall (i in IDX_SET) (i > str_len(x) <-> x[i] = 'eps');

function array[IDX_SET] of ALPHABET:
to_var(array[int] of ALPHABET: x) ::promise_total = 
  [if i > length(x) then 'eps' else x[i] endif | i in IDX_SET];

function var int: 
str_len(array[IDX_SET] of var ALPHABET: x) ::promise_total = let {
  var 0..MAX_STR_LEN: l;
} in l;

predicate 
str_eq(array[IDX_SET] of var ALPHABET: x, array[IDX_SET] of var ALPHABET: y) =
  str_len(x) = str_len(y) /\ x = y;

function array[IDX_SET] of var ALPHABET:
str_cat(array[IDX_SET] of var ALPHABET: x, array[IDX_SET] of var ALPHABET: y) 
::promise_total = let {
  var 0..MAX_STR_LEN: lx = str_len(x);
  var 0..MAX_STR_LEN: ly = str_len(y);
  array[IDX_SET] of var ALPHABET: z;
  constraint str_var(z) /\ str_len(z) = lx + ly;
  constraint forall (i in IDX_SET) (i > lx \/ x[i] = z[i]);
  constraint forall (i in IDX_SET) (i > ly \/ y[i] = z[i+lx]);
} in z;


array[IDX_SET] of var ALPHABET: J;
constraint str_var(J);
array[IDX_SET] of var ALPHABET: I;
constraint str_var(I);
array[IDX_SET] of var ALPHABET: K;
constraint str_var(K);
array[IDX_SET] of var ALPHABET: R;
constraint str_var(R);
array[IDX_SET] of var ALPHABET: G;
constraint str_var(G);
array[IDX_SET] of var ALPHABET: L;
constraint str_var(L);
array[IDX_SET] of var ALPHABET: N;
constraint str_var(N);
array[IDX_SET] of var ALPHABET: M;
constraint str_var(M);
array[IDX_SET] of var ALPHABET: P;
constraint str_var(P);
constraint str_eq(
	str_cat((J), str_cat((to_var(['a', 'a'])), str_cat((J), str_cat((to_var(['a', 'b'])), str_cat((N), str_cat((L), str_cat((to_var(['a'])), str_cat((K), str_cat((to_var(['b'])), str_cat((P), str_cat((P), (to_var(['b', 'a']))))))))))))),
	str_cat((to_var(['a'])), str_cat((G), str_cat((I), str_cat((to_var(['a', 'a'])), str_cat((M), str_cat((M), str_cat((M), str_cat((M), str_cat((to_var(['b', 'a', 'a', 'a', 'a', 'b'])), str_cat((R), str_cat((R), (to_var(['b', 'a', 'a'])))))))))))))
);
% Modifications by MiniZinc Challenge Organizers:
% - Add an arbitrary fixed value for MAX_STR_LEN
% - Add an objective value to transform into an optimisation problem
% - Add a search annotation
% - Add a par definition of str_len
MAX_STR_LEN = 60;
include "globals.mzn";
function int: str_len(array[IDX_SET] of ALPHABET: x) = count (i in IDX_SET) (x[i] != 'eps');
var int: objective = sum([
  nvalue([x | x in J where x != 'eps']),
  nvalue([x | x in I where x != 'eps']),
  nvalue([x | x in K where x != 'eps']),
  nvalue([x | x in R where x != 'eps']),
  nvalue([x | x in G where x != 'eps']),
  nvalue([x | x in L where x != 'eps']),
  nvalue([x | x in N where x != 'eps']),
  nvalue([x | x in M where x != 'eps']),
  nvalue([x | x in P where x != 'eps'])
]);
solve :: int_search(
  [[J[idx], I[idx], K[idx], R[idx], G[idx], L[idx], N[idx], M[idx], P[idx]][v] | idx in IDX_SET, v in 1..9],
  input_order,
  indomain_max
) maximize objective;


