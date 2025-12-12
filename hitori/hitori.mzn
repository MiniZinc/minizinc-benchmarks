% Hitori https://www.puzzle-hitori.com/
int: n; % size of square
set of int: ROW = 1..n;
set of int: COL = 1..n;
set of int: NUM = 1..n;
set of int: NUM0 = 0..n;
array[ROW,COL] of NUM: clue;

% decisions, which squares are marked as black
array[ROW,COL] of var bool: filled;
array[ROW,COL] of var NUM0: x =
  [(r,c): if filled[r,c] then 0 else clue[r,c] endif | r in ROW, c in COL];

% never black out clues that appear once in row and column
/*
include "count.mzn";
constraint forall(r in ROW, c in COL)
                 (if count(clue[r,..],clue[r,c]) = 1
                     /\ count(clue[..,c],clue[r,c]) = 1 
                 then filled[r,c] = false endif);
*/
%% if two identical clues are adjacent all equal clue values in
%% the row/col have to be filled in (since one of these two will not be)
constraint forall(r in ROW)
                 (let { int: cc = arg_max(
                        [ clue[r,c] = clue[r,c+1] | c in 1..n-1 ] 
                        ++ [true]); } in
                  if cc < n then
                     forall(c in 1..n where c != cc /\ c != cc + 1 /\ 
                                      clue[r,c] = clue[r,cc])(filled[r,c])
                  endif);
constraint forall(c in COL)
                 (let { int: rr = arg_max(
                        [ clue[r,c] = clue[r+1,c] | r in 1..n-1 ] 
                        ++ [true]); } in
                  if rr < n then
                     forall(r in 1..n where r != rr /\ r != rr + 1 /\ 
                                      clue[r,c] = clue[rr,c])(filled[r,c])
                  endif);
%% a cell between two identical cells cannot be filled
constraint forall(r in 2..n-1, c in COL)
                 (if clue[r-1,c] = clue[r+1,c] then not filled[r,c] endif);
constraint forall(r in ROW, c in 2..n-1)
                 (if clue[r,c-1] = clue[r,c+1] then not filled[r,c] endif);
%% simple corners
constraint if clue[1,1] = clue[1,2] /\ clue[1,1] = clue[2,1] then filled[1,1] endif;
constraint if clue[1,n] = clue[1,n-1] /\ clue[1,n] = clue[2,n] then filled[1,n] endif;
constraint if clue[n,1] = clue[n,2] /\ clue[n,1] = clue[n-1,1] then filled[n,1] endif;
constraint if clue[n,n] = clue[n-1,n] /\ clue[n,n] = clue[n,n-1] then filled[n,n] endif;
                                                                                                                                       
                        
include "alldifferent_except_0.mzn";
constraint forall(r in ROW)
                 (alldifferent_except_0(x[r,..]));
constraint forall(c in COL)
                 (alldifferent_except_0(x[..,c]));

constraint forall(r in ROW)
                 (forall(c in 1..n-1)
                        (not filled[r,c] \/ not filled[r,c+1]));
constraint forall(c in COL)
                 (forall(r in 1..n-1)
                        (not filled[r,c] \/ not  filled[r+1,c]));            
      
int: digits = ceil(log(10,n+1));
string: block = concat([ "#" | i in 1..digits]);                             
output [ if fix(x[r,c]) = 0 then block else show_int(digits,x[r,c]) endif ++
         if c = n then "\n" else "," endif 
       | r in ROW, c in COL ];
output ["obj = \(obj);\n"];
output ["nofilled = \(sum(filled));\n"];       
%output [show2d(clue)];

include "globals.mzn";
set of int: NODE = 1..n*n;
array[int] of NODE: from = 
    [ (r-1)*n + c | r in ROW, c in COL, j in 1..(c<n)+(r<n) ];
array[int] of NODE: to = 
    [ if (c<n) /\ (r<n) then 
         if j = 1 then (r-1)*n + c+1 
         else r*n+c endif
      elseif c<n then
         (r-1)*n + c+1
      else
         r*n+c
      endif         
    | r in ROW, c in COL, j in 1..(c<n)+(r<n) ];
set of int: EDGE = index_set(from);

ROW: toROW(NODE: i) = (i-1) div n + 1;
COL: toCOL(NODE: i) = (i-1) mod n + 1;

array[EDGE] of var bool: edge =
   [ not filled[toROW(from[e]),toCOL(from[e])]
     /\ not filled[toROW(to[e]),toCOL(to[e])]
   | e in EDGE ];    
%output ["from = \(from);\n  to = \(to)\n"]; 

constraint connected(from,to,[ not filled[r,c] | r in ROW, c in COL ],edge);

% Par version of connected to ensure solution checking works
test connected(
  array [$$E] of $$N: from,
  array [$$E] of $$N: to,
  array [$$N] of bool: ns,
  array [$$E] of bool: es,
) = let {
   any: root = [i | i in index_set(ns) where ns[i]][1];
} in reachable_nodes(root, {root}, from, to, ns, es) == {i | i in index_set(ns) where ns[i]};

function set of $$N: reachable_nodes(
  $$N: node,
  set of $$N: seen,
  array [$$E] of $$N: from,
  array [$$E] of $$N: to,
  array [$$N] of bool: ns,
  array [$$E] of bool: es,
) = let {
  any: adjacent = {n | i in index_set(es) where es[i] /\ (from[i] == node \/ to[i] == node), n in [from[i], to[i]] where n != node} diff seen;
  any: seen_next = seen union adjacent;
} in seen union {x | adj in adjacent, x in reachable_nodes(adj, seen_next, from, to, ns, es)};

var int: obj = sum(r in ROW, c in COL)(filled[r,c]*clue[r,c]);            
solve :: bool_search(filled, input_order, indomain_max) maximize obj;

