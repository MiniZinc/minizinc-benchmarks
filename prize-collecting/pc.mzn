int: n; % size
array[1..n,  0..n] of int: p;

array[1..n] of var 0..n: next;% next posn in tour : 
                              % 1 for last edge, 0 for unused

int : max_obj = sum(i in 1..n)(max(0,max([p[i, j] | j in 1..n])));

array[1..n] of var 0..n: pos; % posn of node i in path, 0 = notin
var 0..max_obj : obj;
array[1..n] of var int : prize;

constraint pos[1] = 1;

constraint forall(i in 1..n) (
  % if used, the next position in tour is non-zero
  ( pos[i] > 0 <-> next[i] > 0 ) /\

  % Except if unused, there is at most 1 node with i as its successor
  ( sum(k in 1..n) (bool2int(next[k] = i)) <= 1) /\

  % next[i] > 1 means used, and not last
  ( next[i] > 1 -> pos[next[i]] = pos[i]+1 ) /\

  ( prize[i] = p[i, next[i]]  )
);

constraint obj = sum(i in 1..n)(prize[i]);

solve 
  :: seq_search([int_search(next, largest, indomain_max, complete),
  int_search(pos, largest, indomain_max, complete),
  int_search(prize, largest, indomain_max, complete),
  int_search([obj], input_order, indomain_max, complete)])
  maximize obj;

output [  "pos = ", show(pos), "\n",
          "prize = ", show(prize), "\n",
          "next = ", show(next), "\n",
          "obj = ", show(obj), "\n"
       ];
