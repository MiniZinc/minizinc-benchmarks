% ============= DATA DEFINITION =============================

% Max time horizon
int: time_horizon;
% Total number of generators
int: num_of_generators;
% Total number of loads
int: num_of_loads;

% Set of time periods
set of int: TIME = 1..time_horizon;
% Set of generators
set of int: GEN = 1..num_of_generators;
% Set of loads
set of int: LOAD = 1..num_of_loads;

% Generation capacity
array[GEN, TIME] of int: gen_max;
% Minimum generation (if on)
array[GEN, TIME] of int: gen_min;
% Initial commitment status
array[GEN] of int: init_commitment;
% Active load demand
array[LOAD, TIME] of int: demand;
% Generation marginal costs
array[GEN, TIME] of int: dispatch_cost;
% Commitment start-up costs
array[GEN] of int: startup_cost;
% Shutdown costs
array[GEN] of int: shutdown_cost;
% Load shedding costs/penalty
array[LOAD] of int: shed_cost;
% Ramp capability 
array[GEN] of int: max_ramp_rate;
% Minimum downtime for generators  
array[GEN] of int: min_down;
% Maximum number of start up for generators
array[GEN] of int: max_num_start;

% ============= END DATA DEFINITION =============================

% ============= VARIABLE DEFINITION =============================

% Commitment of generators
array[GEN, TIME] of var bool: commitment;
% Generator generating level
array[GEN, TIME] of var 0..max(g in GEN, t in TIME)(gen_max[g,t]): generation;
% Loss of load
array[LOAD, TIME] of var 0..max(g in GEN, t in TIME)(gen_max[g,t]): loss_of_load;
% Auxiliary variable to indicate start-up/shut-down logic 
array[GEN, TIME] of var bool: up;
array[GEN, TIME] of var bool: down;



% ============= END VARIABLE DEFINITION =============================

% ============= CONSTRAINT DEFINITION =============================

% Dispatch max
constraint forall(g in GEN, t in TIME)(
  generation[g,t] <= gen_max[g,t] * commitment[g,t]
);

% Dispatch min
constraint forall(g in GEN, t in TIME)(
  generation[g,t] >= gen_min[g,t] * commitment[g,t]
);

% Loss of load max
constraint forall(l in LOAD, t in TIME)(
  loss_of_load[l,t] <= demand[l,t]
);

constraint forall(g in GEN)(
  commitment[g,1] == init_commitment[g]
);

constraint forall(g in GEN)(
  up[g,1] == 0 
);

constraint forall(g in GEN)(
  down[g,1] == 0 
);

% Start-up/Shut-down commitment logic
constraint forall(g in GEN, t in TIME where t > 1)(
  up[g,t] == (commitment[g,t] /\ not commitment[g,t-1]) 
);
constraint forall(g in GEN, t in TIME where t > 1)(
  down[g,t] == (commitment[g,t-1] /\ not commitment[g,t]) 
);


% Copper plate one-bus simplified power-flow model
constraint forall(t in TIME)(
  sum(g in GEN)(generation[g,t]) == sum(l in LOAD)(demand[l,t] - loss_of_load[l,t])
);
% Ramping constraints
constraint forall(g in GEN, t in TIME where t > 1)(
  (not up[g,t]) -> (generation[g,t] - generation[g,t-1] <= max_ramp_rate[g])
);  
constraint forall(g in GEN, t in TIME where t > 1)(
  (not down[g,t]) -> (generation[g,t] - generation[g,t-1] >= -1 * max_ramp_rate[g])
);

% Minimum downtime constraints
constraint forall(g in GEN)(
    forall(t in TIME)(
        down[g,t] -> forall(j in t+1..t+min_down[g] where j in TIME)(not commitment[g,j])
    )
);
% Maximum generator start-up constraints (U.S. DoE emission)
constraint forall(g in GEN)(
    count(t in TIME)(up[g,t]) <= max_num_start[g]
);
int: max_possible_obj = 
   min(2147483646,
     sum(g in GEN, t in TIME)(dispatch_cost[g,t] * gen_max[g,t]) +
     sum(g in GEN, t in TIME)(max(startup_cost[g], shutdown_cost[g])) +
     sum(l in LOAD, t in TIME)(shed_cost[l] * demand[l,t])
   );
   
var 0..max_possible_obj: obj = 
   sum(g in GEN, t in TIME)(dispatch_cost[g,t] * generation[g,t]) +
   sum(g in GEN, t in TIME)(startup_cost[g] * up[g,t]) +
   sum(g in GEN, t in TIME)(shutdown_cost[g] * down[g,t]) +
   sum(l in LOAD, t in TIME)(shed_cost[l] * loss_of_load[l,t]) ;


solve :: seq_search([
             bool_search(commitment, smallest, indomain_split),
             bool_search(up, smallest, indomain_split),
             bool_search(down, smallest, indomain_split),
             int_search(loss_of_load, smallest, indomain_min),
             int_search(generation, smallest, indomain_split)             
             ])
minimize obj; 

