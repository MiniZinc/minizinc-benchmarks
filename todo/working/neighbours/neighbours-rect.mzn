%------------------------------------------------------------------------------%
% Neighbours Problem (taken and adapted from the IBM Challenge "Ponder This")
%
% IBM Challenge "Ponder This" (main website):
%   https://www.research.ibm.com/haifa/ponderthis/index.shtml
% Neighbours Problem Challenge:
%   https://www.research.ibm.com/haifa/ponderthis/challenges/December2012.html
%
% There are living n*m people in a nxm grid, and each of them lives in a
% separate square of the grid. Each resident's neighbours are those who live
% in the squares that have a common edge with that resident's square. For 
% instance, the neighbours of resident E are B, D, F, and H in the grid below.
%
% +---+---+---+
% | A | B | C |
% +---+---+---+
% | D | E | F |
% +---+---+---+
% | G | H | J |
% +---+---+---+
%
% Each resident of the grid is assigned a natural number N, such that if a
% person receives some N>1, then he or she must also have neighbours that
% have been assigned all of the numbers 1, 2, ..., N-1.
%
% Find a configuration (assignment of numbers) of all neighbours, so that
% the sum of their numbers are maximised.
%
% Submitter: Peter J. Stuckey
%
% Modified by MiniZinc team:
%   - Beautification of code
%   - Addition of an output item
%   - Fixing symmetry breaking constraints for non-squared grids
%   - Changed search heuristic
%------------------------------------------------------------------------------%
% Includes

include "lex_lesseq.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n;     % The number of rows
int: m;     % The number of columns

set of int: Rows = 1..n;    % The set of rows
set of int: Cols = 1..m;    % The set of columns

%------------------------------------------------------------------------------%
% Variables

array[Rows,Cols] of var 1..5: x;    % The number of residents
var n*m..5*n*m: objective;          % The total number of all residents


%------------------------------------------------------------------------------%
% Auxiliary functions, predicates, and tests

    % Testing wether the square (i,j) lies in the grid
    %
test is_in_grid(int: i, int: j) = (
    1 <= i /\ i <= n /\ 1 <= j /\ j <= m
);

    % Testing whether the square (i1,j1) is the number of (i,j) assuming that
    % (i,j) lies in the grid
test is_neighbour(int: i, int: j, int: i1, int: j1) = (
    is_in_grid(i1, j1) /\ abs(i-i1) + abs(j-j1) = 1
);

    % Returns all neighbours of (i,j) in a 2-dimensional array where the 2nd
    % dimension records the neighbours coordinates
function array[int,1..2] of int: get_neighbours(int: i, int: j) =
    let {
        int: count = sum(i1 in i-1..i+1, j1 in j-1..j+1 where is_neighbour(i, j, i1, j1))(1);
        array[1..count,1..2] of int: neigh = array2d(1..count,1..2,
            [ [i1, j1][p] 
            | i1 in i-1..i+1, j1 in j-1..j+1, p in 1..2 where is_neighbour(i, j, i1, j1) ]
        );
    } in neigh;

%------------------------------------------------------------------------------%
% Auxiliary predicates for symmetry breaking

predicate var_perm_sym(array[int] of var int: x, array[int,int] of int: p) =
    let { 
        int: l = min(index_set_1of2(p)),
        int: u = max(index_set_1of2(p)),
	    array[1..length(x)] of var int: y = [ x[i] | i in index_set(x) ] 
    } in (
        forall (i, j in l..u where i != j) (
            var_perm_sym_pairwise(
                y,
                [ p[i,k] | k in index_set_2of2(p) ],
                [ p[j,k] | k in index_set_2of2(p) ]
            )
        )
    );

predicate var_perm_sym_pairwise( array[int] of var int: x, array[int] of int: p1, array[int] of int: p2) =
    let { 
        int: n = length(x),
        array[1..n] of 1..n: invp1 = [ j | i, j in 1..n where p1[j] = i ] 
    } in ( 
        lex_lesseq(x, [ x[p2[invp1[i]]] | i in 1..n ])
    );

    % Symmetry breaking constraints for squared grids
    %
predicate var_sqr_sym(array[int,int] of var int: x) =
    let { 
        int: n1 = card(index_set_1of2(x));
        int: n2 = card(index_set_2of2(x));
        constraint assert(n1 = n2,"square symmetry applied to non-square array");
        int: l = n1 * n1;
        array[1..l] of var int: y = [ x[i,j] | i in index_set_1of2(x), j in index_set_2of2(x) ];
        array[1..8,1..l] of 1..l: p = array2d(1..8,1..l,
            [ 
                if     k == 1 then i*n1 + j - n1 
                elseif k == 2 then (n1 - j)*n1 + i            % r270
                elseif k == 3 then (n1 - i)*n1 + (n1 - j + 1) % r180
                elseif k == 4 then (j*n1 - n1) + (n1 - i + 1) % r90
                elseif k == 5 then (n1 - i)*n1 + j            % x flip
                elseif k == 6 then (i*n1 - n1) + (n1 - j + 1) % y flip
                elseif k == 7 then (n1 - j)*n1 + (n1 - i + 1) % d2 flip
                else               (j*n1 - n1) + i            % d1 flip
                endif
            | k in 1..8, i, j in 1..n1
            ]
        ); 
    } in (
        var_perm_sym(y, p)
    );

    % Symmetry breaking constraints for non-squared grids
    %
predicate var_rect_sym(array[int,int] of var int: x) =
    let { 
        int: n1 = card(index_set_1of2(x));
        int: m1 = card(index_set_2of2(x));
        int: l = n1 * m1;
        array[1..l] of var int: y = [x[i,j] | i in index_set_1of2(x), j in index_set_2of2(x)];
        array[1..3, 1..l] of 1..l: p = array2d(1..3, 1..l,
            [ 
                if     k == 1 then i*m1 + j - m1
                elseif k == 2 then (n1 - i)*m1 + j             % x flip
                else               (i*m1 - m1) + (m1 - j + 1)  % y flip
                endif
            | k in 1..3, i in 1..n1, j in 1..m1
            ]
        ); 
    } in (
        var_perm_sym(y,p)
    );

%------------------------------------------------------------------------------%
% Constraints

    % Neighbouring constraints
    %
constraint forall(i in Rows, j in Cols)(
    let { 
        array[int,1..2] of int: neigh = get_neighbours(i, j);
        set of int: Neighs = index_set_1of2(neigh);
    } in (
        true
    %/\  trace("(\(i),\(j)): \(get_neighbours(i,j))\n")
    /\  forall(num in 2..5)(
            x[i,j] >= num -> exists(c in Neighs)(x[neigh[c,1], neigh[c,2]] = num - 1)
        )
    )
);

    % Constraining the objective to the sum of the resident numbers in the grid
    %
constraint objective = sum(i in Rows, j in Cols)(x[i,j]);


    % Redundant constraints restricting the number of resident
    % living on the grid border
constraint redundant_constraint(
    % Residents living in the grid corners can have at most 3 as their number
    x[1,1] <= 3 /\ x[n,1] <= 3 /\ x[1,m] <= 3 /\ x[n,m] <= 3
    % Residents living on the grid borders can have at most 4 as their number
/\  forall(i in Rows)( x[i,1] <= 4 /\ x[i,m] <= 4)
/\  forall(j in Cols)( x[1,j] <= 4 /\ x[n,j] <= 4)
);

    % Symmetry breaking constraints
    %
constraint symmetry_breaking_constraint(
    if n = m then var_sqr_sym(x) else var_rect_sym(x) endif
);
                                    
% Solve item

solve 
    :: int_search(array1d(x), largest, indomain_max, complete)
    %:: int_search(array1d(x), first_fail, indomain_max, complete)
    maximize objective;               
                                     
%------------------------------------------------------------------------------%
% Output

output [
    if c = 1 then "% " else "" endif
++  "\(x[r,c])"
++  if c = m then "\n" else " " endif
| r in Rows, c in Cols
] ++ [
    "x = array2d(\(Rows),\(Cols),\(x));\n",
    "objective = \(objective);\n"
];

