%------------------------------------------------------------------------------
% Parameters

int: num_strings;
int: max_length_strings;
int: max_char;

int: max_length_median;

array [1..num_strings, 1..max_length_strings] of int: strings;
array [1..num_strings] of int: str_length;


%------------------------------------------------------------------------------
% Variables

array [1..max_length_strings] of var 0..max_char: median;
array [1..num_strings] of var 0..2*max_length_strings: distances;

int: obj_ub = num_strings * 2 * max_length_strings;
var 0..obj_ub: objective;

%------------------------------------------------------------------------------
% Predicates

predicate lcs_global(array[int] of var int: S1, array[int] of var int: S2, var int: ED) =

	  let { int: l1 = min(index_set(S1)) - 1;
	        int: l2 = min(index_set(S2)) - 1;
		int: u1 = max(index_set(S1));
		int: u2 = max(index_set(S2));
		array[l1..u1,l2..u2] of var 0..u1+u2: T; } in
	  T[l1,l2] = 0 /\
	  T[u1,u2] = ED /\
	  forall(i in l1+1..u1, j in l2+1..u2)
	        (T[i,j] >= 0 /\ T[i,j] <= i+j) /\
	  forall(j in l2+1..u2)(T[l1,j] = j-l2) /\
	  forall(i in l1+1..u1)(T[i,l2] = i-l1) /\
	  forall(i in l1+1..u1, j in l2+1..u2)
		(T[i,j] = if S1[i] = S2[j] then
		       	    T[i-1,j-1]
		       	  else
		       	    if S1[i] = 0 then
		       	      T[i-1,j]
		       	    else
		       	      if S2[j] = 0 then
		       	        T[i,j-1]
		       	      else
		       	        min([T[i-1,j]+1,T[i,j-1]+1])
		       	      endif
  		       	  endif
			        endif
		);
		
%------------------------------------------------------------------------------
% Constraints

constraint forall(i in 1..num_strings)(
    lcs_global([strings[i,j] | j in 1..max_length_strings], median, distances[i])
);

constraint forall(i in max_length_median+1..max_length_strings)(
  median[i] = 0
);

constraint objective = sum(i in 1..num_strings)(distances[i]);

%------------------------------------------------------------------------------
% Solve item

solve 
    :: int_search(median, input_order, indomain_min, complete) 
    minimize objective;

%------------------------------------------------------------------------------
% Output

output [
    "median = \(median);\n",
    "objective = \(objective);\n"
];
