%%% Original model %%%
% var string: B;
% var string: A;
% constraint
%   ((A) ++ ("a") ++ (A) ++ ("b") ++ (B)) =
%     (("a") ++ (A) ++ (B) ++ (B) ++ ("baa"));
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


array[IDX_SET] of var ALPHABET: B;
constraint str_var(B);
array[IDX_SET] of var ALPHABET: A;
constraint str_var(A);
constraint str_eq(
	str_cat((A), str_cat((to_var(['a'])), str_cat((A), str_cat((to_var(['b'])), (B))))),
	str_cat((to_var(['a'])), str_cat((A), str_cat((B), str_cat((B), (to_var(['b', 'a', 'a']))))))
);
% Modifications by MiniZinc Challenge Organizers:
% - Add an arbitrary fixed value for MAX_STR_LEN
% - Add an objective value to transform into an optimisation problem
% - Add a search annotation
% - Add a par definition of str_len
MAX_STR_LEN = 40;
include "globals.mzn";
function int: str_len(array[IDX_SET] of ALPHABET: x) = count (i in IDX_SET) (x[i] != 'eps');
var int: objective = sum([
  nvalue([x | x in B where x != 'eps']),
  nvalue([x | x in A where x != 'eps'])
]);
solve :: int_search(
  [[B[idx], A[idx]][v] | idx in IDX_SET, v in 1..2],
  input_order,
  indomain_max
) maximize objective;


