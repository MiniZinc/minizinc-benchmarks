%%% Original model %%%
% var string: H;
% var string: G;
% var string: F;
% constraint
%   ((F) ++ (F) ++ ("a") ++ (F) ++ (F) ++ ("baab") ++ (H)) =
%     (("aaaaaa") ++ (G) ++ ("a") ++ (G) ++ ("baabaa"));
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


array[IDX_SET] of var ALPHABET: H;
constraint str_var(H);
array[IDX_SET] of var ALPHABET: G;
constraint str_var(G);
array[IDX_SET] of var ALPHABET: F;
constraint str_var(F);
constraint str_eq(
	str_cat((F), str_cat((F), str_cat((to_var(['a'])), str_cat((F), str_cat((F), str_cat((to_var(['b', 'a', 'a', 'b'])), (H))))))),
	str_cat((to_var(['a', 'a', 'a', 'a', 'a', 'a'])), str_cat((G), str_cat((to_var(['a'])), str_cat((G), (to_var(['b', 'a', 'a', 'b', 'a', 'a']))))))
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
  nvalue([x | x in H where x != 'eps']),
  nvalue([x | x in G where x != 'eps']),
  nvalue([x | x in F where x != 'eps'])
]);
solve :: int_search(
  [[H[idx], G[idx], F[idx]][v] | idx in IDX_SET, v in 1..3],
  input_order,
  indomain_max
) maximize objective;


