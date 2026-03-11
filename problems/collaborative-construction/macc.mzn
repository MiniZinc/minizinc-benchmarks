% Multi-agent Collective Construction (MACC)
% 
% The multi-agent collective construction problem tasks agents to construct any
% given three-dimensional structure on a grid by repositioning blocks. Agents
% are required to also use the blocks to build ramps in order to access the
% higher levels necessary to construct the building, and then remove the ramps
% upon completion of the building.
%
% Further details on the problem can be found in:
% Lam, E., Stuckey, P., Koenig, S., & Kumar, T. K. S. Exact Approaches
% to the Multi-Agent Collective Construction Problem. CP2020.
% https://ed-lam.com/papers/macc2020.pdf
%
% Edward Lam <edward.lam@monash.edu>

% --------
% Instance
% --------

int: A;                       % Number of agents
int: T;                       % Time horizon
int: X;                       % Width
int: Y;                       % Depth
int: Z;                       % Height
array[YY,XX] of ZZ: building; % Structure to construct

% -----------
% Environment
% -----------

set of int: TT = 0..T-1;
set of int: TTT = 0..T-2;
set of int: GRID = 0..X*Y-1;
set of int: XX = 0..X-1;
set of int: YY = 0..Y-1;
set of int: ZZ = 0..Z-1;

array[XX,YY] of GRID: id = array2d(XX, YY, [x*Y + y | y in YY, x in XX]);
set of GRID: BORDER = {id[x,0]   | x in XX} union 
                      {id[x,Y-1] | x in XX} union 
                      {id[0,y]   | y in YY} union 
                      {id[X-1,y] | y in YY};
set of GRID: INTERIOR = GRID diff BORDER;

set of int: OFFGRID = -2..-1;
set of int: WORLD = GRID union OFFGRID;
array[GRID] of set of OFFGRID: off_grid_neighbour = array1d(GRID,
  [(if x == 0                       then {-1,-2} else {} endif) union 
   (if x == X-1                     then {-1,-2} else {} endif) union 
   (if y == 0 /\ 0 < x /\ x < X-1   then {-1,-2} else {} endif) union 
   (if y == Y-1 /\ 0 < x /\ x < X-1 then {-1,-2} else {} endif) 
   | y in YY, x in XX]
);

array[GRID] of set of GRID: neighbours = array1d(GRID, 
  [(if x > 0   then {id[x-1,y]} else {} endif) union 
   (if x < X-1 then {id[x+1,y]} else {} endif) union 
   (if y > 0   then {id[x,y-1]} else {} endif) union 
   (if y < Y-1 then {id[x,y+1]} else {} endif) 
   | y in YY, x in XX]
);
array[GRID] of set of GRID: neighbours_and_self = array1d(GRID, [neighbours[i] union {i} | i in GRID]);
array[GRID] of set of WORLD: world_neighbours_and_self = array1d(GRID, [neighbours_and_self[i] union off_grid_neighbour[i] | i in GRID]);

array[WORLD] of min(WORLD)..max(XX): x_of_pos = array1d(WORLD, [i | i in OFFGRID] ++ [x | y in YY, x in XX]);
array[WORLD] of min(WORLD)..max(YY): y_of_pos = array1d(WORLD, [i | i in OFFGRID] ++ [y | y in YY, x in XX]);

enum ACTION = { 
  UNUSED,
  MOVE,
  BLOCK
};

% -----------------------
% Environment constraints
% -----------------------

% Height of the positions at each time step
array[TT,WORLD] of var ZZ: pos_height;

% Height is 0 outside the map
constraint forall(t in TT, i in OFFGRID) (
  pos_height[t,i] == 0
);

% Height is 0 at the border
constraint forall(t in TT, i in BORDER) (
  pos_height[t,i] == 0
);

% Height is 0 at the first two time steps
constraint forall(t in min(TT)..min(TT)+1, i in GRID) (
  pos_height[t,i] == 0
);

% Height is equal to the building at the last two time steps
constraint forall(t in max(TT)-1..max(TT), i in GRID) (
  pos_height[t,i] == building[y_of_pos[i],x_of_pos[i]]
);

% Change in height
constraint forall(t in TTT, i in GRID) (
  pos_height[t,i] - 1 <= pos_height[t+1,i]
);
constraint forall(t in TTT, i in GRID) (
  pos_height[t+1,i] <= pos_height[t,i] + 1
);

% -----------------
% Agent constraints
% -----------------

% Action of the agents at each position and time step
array[TT,WORLD] of var ACTION: agent_action;
array[TT,WORLD] of var WORLD: agent_next_position;
array[TT,GRID] of var GRID: agent_block_position;
array[TT,WORLD] of var bool: agent_carrying;

array[TTT,GRID] of var bool: agent_pickup;
array[TTT,GRID] of var bool: agent_delivery;

% Fix actions at dummy positions off the map.
constraint forall(t in TT, i in OFFGRID) (
  agent_action[t,i] == MOVE
);

% Fix next positions at dummy positions off the map.
constraint forall(t in TT, i in OFFGRID) (
  agent_next_position[t,i] == i
);

% Fix carrying state at dummy positions off the map.
constraint forall(t in TT) (let {int: i = -1} in
  agent_carrying[t,i] == true
);
constraint forall(t in TT) (let {int: i = -2} in
  agent_carrying[t,i] == false
);

% All agents must be off the grid at the start
constraint forall(i in GRID) (let {int: t = min(TT)} in 
  agent_action[t,i] == UNUSED
);

% All agents must be off the grid at the end
constraint forall(i in GRID) (let {int: t = max(TT)} in
  agent_action[t,i] == UNUSED
);

% Agents must move to a neighbouring position or the same position
constraint forall(t in TT, i in GRID) (
  agent_next_position[t,i] in world_neighbours_and_self[i]
);

% Agents stay at the same position when doing a pickup or delivery.
constraint forall(t in TT, i in GRID) (
  agent_action[t,i] == BLOCK
  ->
  agent_next_position[t,i] == i
);

% Agents cannot pickup or deliver at the same position
constraint forall(t in TT, i in GRID) (
  agent_block_position[t,i] in neighbours[i]
);

% Carrying status
constraint forall(t in TTT, i in GRID) (
  agent_action[t,i] == MOVE
  ->
  agent_carrying[t+1,agent_next_position[t,i]] == agent_carrying[t,i]
);
constraint forall(t in TTT, i in GRID) (
  agent_action[t,i] == BLOCK
  ->
  agent_carrying[t+1,i] == not agent_carrying[t,i]
);

% Carrying status - pickup
constraint forall(t in TTT, i in GRID) (
  agent_pickup[t,i]
  <->
  agent_action[t,i] == BLOCK /\ agent_carrying[t+1,i] /\ not agent_carrying[t,i]
);

% Carrying status - delivery
constraint forall(t in TTT, i in GRID) (
  agent_delivery[t,i]
  <->
  agent_action[t,i] == BLOCK /\ not agent_carrying[t+1,i] /\ agent_carrying[t,i]
);

% Flow out
constraint forall(t in TTT, i in GRID) (
  (agent_action[t,i] == UNUSED)
  \/
  (agent_action[t+1,agent_next_position[t,i]] != UNUSED)
);

% Flow in
constraint forall(t in TTT, i in INTERIOR) (
  agent_action[t+1,i] != UNUSED
  ->
  exists (j in neighbours_and_self[i]) (agent_action[t,j] != UNUSED /\ agent_next_position[t,j] == i)
);

% Vertex collision - limit flows into (t+1,i)
constraint forall(t in min(TT)+1..max(TT)-1, i in GRID) (
  sum(j in neighbours_and_self[i]) (bool2int(agent_action[t,j] == MOVE /\ agent_next_position[t,j] == i)) +
  bool2int(agent_action[t,i] == BLOCK) +
  sum(j in neighbours[i]) (bool2int(agent_action[t+1,j] == BLOCK /\ agent_block_position[t+1,j] == i))
  <= 1
);

% Edge collision
constraint forall(t in min(TT)+1..max(TT)-1, i in GRID) (
  agent_action[t,i] == MOVE /\ agent_next_position[t,i] != i /\ agent_action[t,agent_next_position[t,i]] == MOVE
  ->
  agent_next_position[t,agent_next_position[t,i]] != i
);

% Maximum number of agents
constraint forall(t in min(TT)+1..max(TT)) (
  sum(i in GRID) (bool2int(agent_action[t,i] != UNUSED))
  +
  sum(i in BORDER) (bool2int(agent_action[t-1,i] == MOVE /\ agent_next_position[t-1,i] < 0))
  <= A
);

% ---------------------------
% Interdependence constraints
% ---------------------------

% Height of move
constraint forall(t in TTT, i in GRID) (let {var int: next_pos = agent_next_position[t,i]} in 
  agent_action[t,i] == MOVE
  ->
  pos_height[t,i] - 1 <= pos_height[t+1,next_pos]
);
constraint forall(t in TTT, i in GRID) (let {var int: next_pos = agent_next_position[t,i]} in 
  agent_action[t,i] == MOVE
  ->
  pos_height[t+1,next_pos] <= pos_height[t,i] + 1
);

% Height of wait
constraint forall(t in TTT, i in GRID) (let {var int: next_pos = agent_next_position[t,i]} in 
  agent_action[t,i] == MOVE /\ next_pos == i
  ->
  pos_height[t+1,i] == pos_height[t,i]
);

% Height of pickup
constraint forall(t in TTT, i in GRID) (let {var int: block_pos = agent_block_position[t,i]} in
  agent_pickup[t,i]
  ->
  pos_height[t,block_pos] == pos_height[t,i] + 1
);
constraint forall(t in TTT, i in GRID) (let {var int: block_pos = agent_block_position[t,i]} in
  agent_pickup[t,i]
  ->
  pos_height[t+1,block_pos] == pos_height[t,block_pos] - 1 
);

% Height of delivery
constraint forall(t in TTT, i in GRID) (let {var int: block_pos = agent_block_position[t,i]} in
  agent_delivery[t,i]
  ->
  pos_height[t,block_pos] == pos_height[t,i]
);
constraint forall(t in TTT, i in GRID) (let {var int: block_pos = agent_block_position[t,i]} in
  agent_delivery[t,i]
  ->
  pos_height[t+1,block_pos] == pos_height[t,block_pos] + 1 
);

% Height change
constraint forall(t in TTT, i in GRID) (
  pos_height[t+1,i] == pos_height[t,i]
  - sum(j in neighbours[i]) (bool2int(agent_pickup[t,j]   /\ agent_block_position[t,j] == i))
  + sum(j in neighbours[i]) (bool2int(agent_delivery[t,j] /\ agent_block_position[t,j] == i))
);

% -------------------------------------------
% Symmetry-breaking and redundant constraints
% -------------------------------------------

% Start at the first time step
constraint symmetry_breaking_constraint(exists(i in BORDER) (
  agent_action[min(TT)+1,i] != UNUSED
));

% Height decrease - pickup
constraint forall(t in TTT, i in GRID) (redundant_constraint(
  pos_height[t+1,i] == pos_height[t,i] - 1
  -> 
  exists(j in neighbours[i]) (agent_pickup[t,j] /\ agent_block_position[t,j] == i)
));

% Height increase - delivery
constraint forall(t in TTT, i in GRID) (redundant_constraint(
  pos_height[t+1,i] == pos_height[t,i] + 1
  -> 
  exists(j in neighbours[i]) (agent_delivery[t,j] /\ agent_block_position[t,j] == i)
));

% ------------------
% Objective function
% ------------------

var int: objective = sum(t in TT, i in GRID) (bool2int(agent_action[t,i] != UNUSED));

solve :: seq_search([
  int_search(agent_action,         first_fail, indomain_min, complete),
  int_search(agent_next_position,  first_fail, indomain_min, complete),
  int_search(agent_block_position, first_fail, indomain_min, complete),
  int_search(agent_carrying,       first_fail, indomain_min, complete),
  int_search(pos_height,           first_fail, indomain_min, complete),
]) minimize objective;

output [
  "objective = \(objective);\n",
  "pos_height = array2d(\(TT), \(WORLD), \(pos_height));\n",
  "agent_action = array2d(\(TT), \(WORLD), \(agent_action));\n",
  "agent_next_position = array2d(\(TT), \(WORLD), \(agent_next_position));\n",
  "agent_block_position = array2d(\(TT), \(GRID), \(agent_block_position));\n",
  "agent_carrying = array2d(\(TT), \(WORLD), \(agent_carrying));\n",
  "agent_pickup = array2d(\(TTT), \(GRID), \(agent_pickup));\n",
  "agent_delivery = array2d(\(TTT), \(GRID), \(agent_delivery));\n",
];
