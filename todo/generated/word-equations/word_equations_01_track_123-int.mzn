%%% Original model %%%
% var string: F;
% var string: E;
% constraint
%   (("d") ++ (F) ++ ("bddddaaaaabacaddbdbaca") ++ (F) ++ ("c") ++ (E) ++ ("cad") ++ (F))
%     =
%     (("db") ++ (F) ++ ("ddddaaaaabacadd") ++ (F) ++ ("d") ++ (F) ++ ("acabc") ++ (F) ++ ("aba") ++ (F) ++ ("caaddbda") ++ (F) ++ ("acada") ++ (F) ++ ("babaaabdabcdacad") ++ (F));
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


array[IDX_SET] of var ALPHABET: F;
constraint str_var(F);
array[IDX_SET] of var ALPHABET: E;
constraint str_var(E);
constraint str_eq(
	str_cat((to_var(['d'])), str_cat((F), str_cat((to_var(['b', 'd', 'd', 'd', 'd', 'a', 'a', 'a', 'a', 'a', 'b', 'a', 'c', 'a', 'd', 'd', 'b', 'd', 'b', 'a', 'c', 'a'])), str_cat((F), str_cat((to_var(['c'])), str_cat((E), str_cat((to_var(['c', 'a', 'd'])), (F)))))))),
	str_cat((to_var(['d', 'b'])), str_cat((F), str_cat((to_var(['d', 'd', 'd', 'd', 'a', 'a', 'a', 'a', 'a', 'b', 'a', 'c', 'a', 'd', 'd'])), str_cat((F), str_cat((to_var(['d'])), str_cat((F), str_cat((to_var(['a', 'c', 'a', 'b', 'c'])), str_cat((F), str_cat((to_var(['a', 'b', 'a'])), str_cat((F), str_cat((to_var(['c', 'a', 'a', 'd', 'd', 'b', 'd', 'a'])), str_cat((F), str_cat((to_var(['a', 'c', 'a', 'd', 'a'])), str_cat((F), str_cat((to_var(['b', 'a', 'b', 'a', 'a', 'a', 'b', 'd', 'a', 'b', 'c', 'd', 'a', 'c', 'a', 'd'])), (F))))))))))))))))
);
% Modifications by MiniZinc Challenge Organizers:
% - Add an arbitrary fixed value for MAX_STR_LEN
% - Add an objective value to transform into an optimisation problem
% - Add a search annotation
% - Add a par definition of str_len
MAX_STR_LEN = 20;
include "globals.mzn";
function int: str_len(array[IDX_SET] of ALPHABET: x) = count (i in IDX_SET) (x[i] != 'eps');
var int: objective = sum([
  nvalue([x | x in F where x != 'eps']),
  nvalue([x | x in E where x != 'eps'])
]);
solve :: int_search(
  [[F[idx], E[idx]][v] | idx in IDX_SET, v in 1..2],
  input_order,
  indomain_max
) maximize objective;


