% Blocks World Puzzle
% Model by Mats Carlsson

% Objective variable renamed to objective by MiniZinc Challenge Organisers

% Numbered blocks are stacked into piles.

% The objective is to transform a start configuration into a goal
% configuration by moving one block at a time, with a minimal number
% of moves. Example:

%   Given: 9 cubes, max 3 piles

%   Start configuration:
%     Pile 1: [7, 5, 3, 9]
%     Pile 2: []
%     Pile 3: [8, 4, 6, 1, 2]

%   Goal configuration:
%     Pile 1: [6, 9, 1, 3, 4, 5]
%     Pile 2: [7]
%     Pile 3: [2, 8]

%   n = 9;
%   k = 3;
%   start = [2, 0, 9, 6, 3, 1, 5, 4, 0];
%   end = [3, 8, 4, 5, 0, 9, 0, 0, 1];

include "globals.mzn";

int: n; % number of cubes
int: k; % number of piles

int: nk = n*k; % heuristic max number of moves

set of int: cube = 1..n;
set of int: cube0 = 0..n;
set of int: step = 1..nk;
set of int: step0 = 0..nk;

array[cube] of cube0: start;
array[cube] of cube0: end;

array[cube0, step0] of var cube0: state;
array[cube0, step0] of var 0..k: count;
array[step0] of var bool: done;
array[step, 1..2] of var cube0: move;
array[cube, step0] of var bool: locked =
  array2d(cube, step0, [locked(c,s) | c in cube, s in step0]);
var 0..nk: objective;

constraint
  objective = nk + 1 - sum(done);

constraint
  forall(i in step)(move[i,2] = state[move[i,1],i]);

constraint array1d(state[0,..]) = [0 | _ in step0];

constraint state[cube,0] = start;

constraint state[cube,nk] = end;

constraint increasing(done);

constraint
  forall(c in cube0, i in step0)(
    if c = 0 then count[c,i] >= 1 else count[c,i] <= 1 endif
  );

constraint
  forall(i in step0)(
    global_cardinality_closed( state[cube,i]
                             , array1d(cube0, cube0)
			     , count[..,i]
			     )
  );

constraint
  forall(i in step0)(state[cube,i] = end <-> done[i]);

constraint
  forall(i in step)(
    if done[i-1] then nomove(i-1, i) else move(i-1, i) endif
  );

predicate move(int: i0, int: i) =
    move[i,1] != 0 /\
    forall(c in cube)(state[c,i0] != state[c,i] <-> c = move[i,1]) /\
    count[move[i,1],i0] = 0;

predicate nomove(int: i0, int: i) =
    move[i,1] = 0 /\
    state[..,i0] = state[..,i];

% assume max k moves per cube
constraint
  symmetry_breaking_constraint(
    forall(c in cube where start[c] != end[c])(
      sum(i in step)(state[c,i-1] != state[c,i]) >= 1
    ) /\
    forall(c in cube)(
      sum(i in step)(state[c,i-1] != state[c,i]) <= k
    )
  );

% prevent do-undo
constraint
  symmetry_breaking_constraint(
    forall(i in step where i < nk)(
      (done[i] \/ move[i,1] != move[i+1,1]) /\
      (done[i] \/ move[i,2] != move[i+1,1]) /\
      (done[i] \/ move[i,2] != move[i+1,2]) /\
      (done[i] \/ move[i,1] != move[i,2])
    )
  );

% don't move locked cubes
constraint
  symmetry_breaking_constraint(
    forall(c in cube, i in step0 where i < nk)(
      locked[c, i] -> (state[c, i+1] = end[c] /\ move[i+1, 1] != c)
    )
  );

% objective lower bound
constraint
  symmetry_breaking_constraint(
    forall(s in step0)(done[s] \/ n - sum(locked[.., s]) + s <= objective)
  );

predicate locked(cube: c, step0: s) =
  state[c,s] = end[c] /\
  if end[c] != 0 then locked(end[c], s) else true endif;

solve
  :: int_search(move, input_order, indomain_min)
  minimize objective;
  
