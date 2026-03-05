% Nontaking armies of pieces
%    place knights, rooks, queens, bishops on a n*n chessboard
%    so that none take each other. 
enum PIECE = { N, B, R, Q, e }; % pieces
int: n;                     % size of chessboard
array[PIECE] of int: value; % value of each piece to place
array[PIECE] of int: limit; % limit on each piece to place

set of int: ROW = 1..n;
set of int: COL = 1..n;
array[ROW,COL] of var PIECE: x;


include "global_cardinality.mzn";
array[PIECE] of var 0..n*n: cnt; % counts on each piece
% count the number of pieces used
constraint global_cardinality(array1d(x), PIECE, cnt);
% enforce upper bound
constraint forall(p in PIECE where p != e)(cnt[p] <= limit[p]);
% enforce lower bound on empty
constraint cnt[e] >= n*n - sum(limit) + limit[e];

% if a rook or queen in a ROW nothing else
constraint forall(r in ROW)
                 (exists(c in COL)(x[r,c] in { R, Q }) ->
                  count(c in COL)(x[r,c] != e) <= 1);
% af a rook or queen in a COL nothing else
constraint forall(c in COL)
                 (exists(r in ROW)(x[r,c] in { R, Q }) ->
                  count(r in ROW)(x[r,c] != e) <= 1);
% redundant
constraint cnt[R] + cnt[Q] <= n;

% if a bishop or queen on an up diagonal nothing else
constraint forall(d in 3..2*n-1)  % omit singleton diagonals
                 (exists(r in ROW)(x[r,d-r] in { B, Q }) ->
                  count(r in ROW)(x[r,d-r] != e) <= 1);
% if a bishop or queen on an down diagonal nothing else
constraint forall(d in -n+2..n-2) % omit singleton diagonals
                (exists(r in ROW)(x[r,r+d] in { B, Q }) ->
                 count(r in ROW)(x[r,r+d] != e) <= 1);
% redundant
constraint redundant_constraint(cnt[B] + cnt[Q] <= 2*n-1);

% knights dont take anything
constraint forall(r in ROW, c in COL)
                 (x[r,c] = N ->
                  forall(rr in r-2..r+2, cc in c - 2..c+2 
                         where rr in ROW /\ cc in COL /\ 
                               abs(r - rr) +abs(c - cc) = 3)
                        (x[rr,cc] = e));  
                        
% redundant
constraint redundant_constraint(cnt[N] <= (n*n + 1) div 2);
         
array[ROW,COL] of var 1..5: y;
array[1..5] of var PIECE: svalue = reverse(arg_sort(value)); 
constraint forall(r in ROW, c in COL)(x[r,c] = svalue[y[r,c]]);


solve :: int_search(array1d(y), input_order, indomain_min)
      maximize obj;
var int: obj;
constraint obj = sum(r  in ROW, c in COL)(value[x[r,c]]);

% dominance rules
constraint if value[Q] <= value[B] then cnt[Q] > 0 -> cnt[B] = limit[B] endif;
constraint if value[Q] <= value[R] then cnt[Q] > 0 -> cnt[R] = limit[R] endif;



% remove symmetries of square
constraint symmetry_breaking_constraint(var_sqr_sym(x));

predicate
var_sqr_sym(array[int,int] of var int: x) =
  let { int: n = card(index_set_1of2(x));
        int: n2 = card(index_set_2of2(x));
        constraint assert(n = n2,"square symmetry applied to non-square array");
        int: l = n * n;
        array[1..l] of var int:
          y = [ x[i,j] | i in index_set_1of2(x),
                         j in index_set_2of2(x) ];
        array[1..8,1..l] of 1..l:
          p = array2d(1..8,1..l,
            [ if k == 1 then i*n + j - n 
              elseif k == 2 then (n - j)*n + i           % r270
              elseif k == 3 then (n - i)*n + (n - j)+1   % r180
              elseif k == 4 then (j*n - n) + (n - i + 1) % r90
              elseif k == 5 then (n - i)*n + j           % x flip
              elseif k == 6 then (i*n - n) + (n - j + 1) % y flip
              elseif k == 7 then (n - j)*n + (n - i + 1) % d2 flip
              else               (j*n - n) + i           % d1 flip
              endif
            | k in 1..8, i,j in 1..n]) }
  in
  var_perm_sym(y,p);


include "lex_lesseq.mzn";

predicate var_perm_sym(array[int] of var int: x,
                       array[int,int] of int: p) =
  let { int: l = min(index_set_1of2(p)),
        int: u = max(index_set_1of2(p)),
	array[1..length(x)] of var int:
          y = [ x[i] | i in index_set(x) ] }
  in
  forall (i, j in l..u where i != j) (
    var_perm_sym_pairwise(y,
      [ p[i,k] | k in index_set_2of2(p) ],
      [ p[j,k] | k in index_set_2of2(p) ])
  );

predicate var_perm_sym_pairwise(
    array[int] of var int: x,
    array[int] of int: p1,
    array[int] of int: p2) =
  let { int: n = length(x),
        array[1..n] of 1..n:
          invp1 = [ j | i, j in 1..n
                      where p1[j] = i ] }
  in
  lex_lesseq(x, [ x[p2[invp1[i]]] | i in 1..n ]);
