%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The Vehicle Routing Problem with Location Congestion                                  %
%                                                                                       %
% The Vehicle Routing Problem with Location Congestion (VRPLC) adds cumulative          %
% scheduling constraints on to the standard Pickup and Delivery Problem with Time       %
% Windows (PDPTW).                                                                      %
%                                                                                       %
% The PDPTW is a classical vehicle routing problem that requires vehicles to depart a   %
% central depot to pick up and deliver goods and then return to the depot. Each request %
% is associated with a weight, called its load. All vehicles are identical, and each    %
% vehicle can carry requests up to a maximum total weight, called the vehicle capacity. %
% Every request is also associated with a time frame, called its time window, within    %
% which the request must be serviced. Vehicles can arrive at the location of a request  %
% prior to the opening of its time window but must wait until its time window opens     %
% before commencing service. The VRPLC overlays scheduling constraints on the PDPTW to  %
% restrict the number of requests being serviced at any given time.                     %
%                                                                                       %
% Publication: Edward Lam, Pascal Van Hentenryck (2016): "A branch-and-price-and-check  %
%   model for the vehicle routing problem with location congestion", Constraints,       %
%   21(3), pp 394-412.                                                                  %
%   https://link.springer.com/article/10.1007%2Fs10601-016-9241-2                       %
%                                                                                       %
% Submitter: Edward Lam                                                                 %
%                                                                                       %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

include "cumulative.mzn";
include "circuit.mzn";

%%%%%%%%
% Data %
%%%%%%%%

% Time
int: T;
set of int: TIME = 0..T;

% Vehicles
int: V;
set of int: VEHICLES = 1..V;

% Vehicle capacity
int: Q;
set of int: LOAD = 0..Q;
set of int: NEGLOAD = -Q..Q;

% Locations
int: L;
set of int: LOCATIONS = 1..L;

% Location capacity
int: C;

% Requests and nodes
int: P;
int: R = 2*P;
int: N = R+2*V;
set of int: PICKUPS = 1..P;
set of int: DELIVERIES = P+1..R;
set of int: REQUESTS = 1..R;
set of int: NODES = 1..N;
set of int: RSNODES = 1..R+V;
set of int: SENODES = R+1..N;

% Requests data
array[NODES,NODES] of TIME: time;
array[REQUESTS] of LOCATIONS: l;
array[REQUESTS] of TIME: a;
array[REQUESTS] of TIME: b;
array[REQUESTS] of TIME: s;
array[REQUESTS] of NEGLOAD: q;
array[NODES] of NEGLOAD: qq = q ++ [0 | i in SENODES];

% Bounds on the objective
int: min_obj = card(RSNODES) * min(TIME);
int: max_obj = card(RSNODES) * max(TIME);

%%%%%%%%%%%%%
% Variables %
%%%%%%%%%%%%%

var min_obj..max_obj: objective;            % Objective value

array[NODES] of var VEHICLES: veh;          % Visiting vehicle
array[NODES] of var NODES: succ;            % Next node in route

array[NODES] of var LOAD: load;             % Load after visiting node

array[NODES] of var TIME: arr;              % Arrival time of node
array[NODES] of var TIME: ser;              % Start of service of node
array[NODES] of var TIME: dep;              % Departure time of node

%%%%%%%%%%%%%%%%%%%%%%%
% Request constraints %
%%%%%%%%%%%%%%%%%%%%%%%

% Subtour elimination
constraint circuit(succ);

% Giant tour representation of routes
constraint forall (v in 1..V-1) (succ[R+V+v] == R+(v+1));
constraint succ[R+V+V] == R+1;

% Track vehicle along route
constraint forall (i in RSNODES) (veh[i] == veh[succ[i]]);
constraint forall (v in VEHICLES) (veh[R+v] == v);
constraint forall (v in VEHICLES) (veh[R+V+v] == v);

% Symmetry breaking
constraint symmetry_breaking_constraint(
    forall (v in 1..V-1) (succ[R+v] == R+V+v -> succ[R+(v+1)] == R+V+(v+1))
/\  veh[1] == 1
);

%%%%%%%%%%%%%%%%%%%%
% Time constraints %
%%%%%%%%%%%%%%%%%%%%

% Order time variables
constraint forall (i in REQUESTS) (arr[i] <= ser[i]);
constraint forall (i in REQUESTS) (ser[i] + s[i] <= dep[i]);
constraint forall (i in REQUESTS) (a[i] <= ser[i] /\ ser[i] <= b[i]);

% Fix time at start nodes and end nodes
constraint forall (i in SENODES) (arr[i] == ser[i]);
constraint forall (i in SENODES) (ser[i] == dep[i]);

% Accumulate time along route
constraint forall (i in RSNODES) (dep[i] + time[i,succ[i]] == arr[succ[i]]);

%%%%%%%%%%%%%%%%%%%%
% Load constraints %
%%%%%%%%%%%%%%%%%%%%

% Accumulate loadalong route
constraint forall (i in RSNODES) (load[i] + qq[succ[i]] == load[succ[i]]);

% Fix load at start nodes and end nodes
constraint forall (i in SENODES) (load[i] == 0);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pickup-delivery constraints %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Delivery after pickup
constraint forall (i in PICKUPS) (dep[i] + time[i,P+i] <= arr[P+i]);

% Delivery on same vehicle as pickup
constraint forall (i in PICKUPS) (veh[i] == veh[P+i]);

%%%%%%%%%%%%%%%%%%%%%%%%
% Location constraints %
%%%%%%%%%%%%%%%%%%%%%%%%

% Service resources
constraint forall (ll in LOCATIONS) (cumulative([ser[i] | i in REQUESTS where l[i] == ll],
                                                [s[i]   | i in REQUESTS where l[i] == ll],
                                                [1      | i in REQUESTS where l[i] == ll],
                                                C));

%%%%%%%%%%%%%%%%%%%%%%
% Objective function %
%%%%%%%%%%%%%%%%%%%%%%

constraint objective = sum (i in RSNODES) (time[i,succ[i]]);

%%%%%%%%%
% Solve %
%%%%%%%%%

ann: search = seq_search([
  int_search(succ,  first_fail, indomain_min, complete),
  int_search( ser,    smallest, indomain_min, complete),
  int_search( arr,    smallest, indomain_min, complete),
  int_search( dep,    smallest, indomain_min, complete),
  int_search(load,    smallest, indomain_min, complete),
  int_search( veh,  first_fail, indomain_min, complete),
]);

solve 
    :: search 
    minimize objective;

%%%%%%%%%%%
% Outputs %
%%%%%%%%%%%

output [
    "succ = \(succ);\n",
    "veh = \(veh);\n",
    "load = \(load);\n",
    "arr = \(arr);\n",
    "ser = \(ser);\n",
    "dep = \(dep);\n",
    "objective = \(objective);\n"
];
