%=============================================================================%
% Capacitated Vehicle Routing problem with Time Windows, Service Times and
% Pickup and deliveries
% CP formulation based on Andrea Rendl's work from 2015 and the Routing model
% used by the LNS solver for VRPs in Google's OR Tools
% adapted to use instances for MIP model
%
% Copyright 2021 Haakon H. Rød
% 
% Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
% associated documentation files (the "Software"), to deal in the Software without restriction,
% including without limitation the rights to use, copy, modify, merge, publish, distribute,
% sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions: The above copyright notice and this
% permission notice shall be included in all copies or substantial portions of the Software.  THE
% SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT
% LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
% NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
% DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
% OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
%============================================================================%

include "circuit.mzn";

int: M; % number of nodes in the MIP model
int: K; % number of vehicles in the model

int: NumVehicles = K; % maximum number of vehicles
int: NumCustomers = M;
int: N = 2*K + M;
int: timeBudget = max (j in 1..M) (TimeWindows[j, 2]) + max (i in 1..N) (max([ TravelTime[i,j] | j in 1..N]) ); % the maximal of time that we got
int: maxCapacity = max (j in 1..K) (Capacity[j]); % Capacity of the largest vehicle

array[1..M] of int: Demand;
array[1..N, 1..N] of int: TravelTime;
array[1..M, 1..2] of int: TimeWindows;
array[1..M, 1..2] of int: PDs;
array[1..K] of int: Capacity;

set of int: VEHICLE = 1..NumVehicles;
set of int: CUSTOMER = 1..NumCustomers;
set of int: TIME = 0..timeBudget;
set of int: LOAD = 0..maxCapacity;

% The last nodes represent the start and end nodes for each vehicle (the depots)
set of int: NODES = 1..NumCustomers+2*NumVehicles; 
set of int: DEPOT_NODES = NumCustomers+1..NumCustomers+2*NumVehicles;
set of int: START_DEPOT_NODES = NumCustomers+1..NumCustomers+NumVehicles;
set of int: END_DEPOT_NODES = NumCustomers+NumVehicles+1..NumCustomers+2*NumVehicles;

% =================================================%
% Variables
% =================================================%

% We are essentially taking the model 
array[NODES] of var NODES: successor; 
array[NODES] of var NODES: predecessor; % redundant predecessor variables
array[NODES] of var VEHICLE: vehicle; % which vehicle visits which customer?
array[NODES] of var LOAD: load; % load when arriving at node n in NODES
array[NODES] of var TIME: arrivalTime; % the time at which the vehicle serving node i will arrive at i
array[NODES] of var TIME: departureTime; % the time at which vehicle serving node i departs from i
array[NODES] of var TIME: slack; % We must allow slack
var 0..timeBudget: objective;
var 0..maxCapacity: start_load;

% =================================================%
% Constraints
% =================================================%

% ------ initialization constraints ---- %
% predecessor of start nodes are end nodes. The vehicles are shifted, so that the predecessor of
% vehicle 1 is the end node of vehicle k. This is done so that the circuit constraint can be applied
% to all the 
constraint redundant_constraint(
   forall(n in (NumCustomers+2..NumCustomers+NumVehicles)) (
     predecessor[n] = n + NumVehicles-1
   )
);

constraint redundant_constraint(
   predecessor[NumCustomers+1] = NumCustomers+2*NumVehicles
);

% successors of end nodes are start nodes
constraint 
   forall(n in (NumCustomers+NumVehicles+1..NumCustomers+2*NumVehicles-1)) (
     successor[n] = n-NumVehicles+1 
   );
constraint
   successor[NumCustomers+2*NumVehicles] = NumCustomers+1;

% associate each start/end nodes with a vehicle
constraint 
   forall(n in START_DEPOT_NODES) (
     vehicle[n] = n-NumCustomers
   );
   
constraint 
   forall(n in END_DEPOT_NODES) (
     vehicle[n] = n-NumCustomers-NumVehicles
   );

% vehicles leave the depot at time zero
% constraint 
%    forall(n in START_DEPOT_NODES) (
%      arrivalTime[n] = 0 
%    );

% vehicle load when starting at the depot
% constraint 
%    forall(n in START_DEPOT_NODES) (
%      load[n] = 0 % Demand[n]
%    );


% ------- predecessor/successor constraints --- %
constraint redundant_constraint(
   forall(n in NODES) (
      successor[predecessor[n]] = n
   )
);

constraint redundant_constraint(
   forall(n in NODES) (
      predecessor[successor[n]] = n
   )
);

% alldiff + subtour elimination constraints
constraint 
   circuit(successor);
constraint redundant_constraint(
   circuit(predecessor)
);


% ---- vehicle constraints ------------- %

% vehicle of node i is the same as the vehicle for the predecessor
constraint redundant_constraint(
   forall(n in CUSTOMER) (
      vehicle[predecessor[n]] = vehicle[n]
   )
);
constraint 
   forall(n in CUSTOMER) (
      vehicle[successor[n]] = vehicle[n]
);


% ----- Pickup & Deliveries ------------ %
constraint 
   forall(n in CUSTOMER) (
      vehicle[n] = vehicle[PDs[n, 2]]
);
 
constraint 
   forall(n in CUSTOMER) (
      arrivalTime[n] >= arrivalTime[PDs[n, 2]]
);

% ----- time constraints ------------ %

% Can cumulative be used here or for load?
constraint 
   forall(n in CUSTOMER) (
      arrivalTime[n] + slack[n] + TravelTime[n,successor[n]] == arrivalTime[successor[n]]
   );
constraint
   forall(n in START_DEPOT_NODES) (
      arrivalTime[n] + slack[n] + TravelTime[n,successor[n]] == arrivalTime[successor[n]]
   );

% Time window constraints
constraint
    forall(i in CUSTOMER)(
        arrivalTime[i] >= TimeWindows[i, 1]
    );

constraint
    forall(i in CUSTOMER)(
        arrivalTime[i] <= TimeWindows[i, 2]
    );


% ----- load constraints ------------ %

constraint 
   forall(n in CUSTOMER) (
      load[n] + Demand[n] = load[successor[n]]
   );

constraint
   forall(n in START_DEPOT_NODES) (
      load[n] = load[successor[n]] 
   );

constraint
   forall(n in CUSTOMER) (
      load[n] <= Capacity[vehicle[n]]
   );

% =====================================
% Objective
% =====================================

constraint
objective = sum (depot in END_DEPOT_NODES) (arrivalTime[depot]) - sum (depot in START_DEPOT_NODES) (arrivalTime[depot]);

solve :: seq_search([int_search(successor, first_fail, indomain_split, complete),
		     int_search(vehicle, first_fail, indomain_split, complete),
               int_search(arrivalTime, first_fail, indomain_min, complete)
              ])   
minimize objective; % traveltime
% solve :: int_search(successor, first_fail, indomain_split, complete) minimize objective;



% ===================================== %
% Output
% ===================================== %

output 
   [ "objective = "] ++ [show(objective)] ++
   [ ";\nvehicle = " ] ++ [ show(vehicle) ]++
   [ ";\nLoad= " ] ++ 
   [ show(load) ]  ++ 
   [ ";\narrivalTime = " ] ++ 
   [ show(arrivalTime) ]  ++ 
   [ ";\nsuccessor = "] ++          [ show(successor) ] ++
%            | n in NODES  ++
   [ ";\n"]
;
