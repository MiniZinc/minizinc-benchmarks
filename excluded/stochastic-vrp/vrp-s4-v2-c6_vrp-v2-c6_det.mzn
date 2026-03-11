include "circuit.mzn";
int: nbVehicles = 2;
int: nbCustomers = 6;
int: timeBudget = 50;
set of int: VEHICLE = 1..nbVehicles;
set of int: CUSTOMER = 1..nbCustomers;
set of int: TIME = 0..timeBudget;
set of int: NODES = 1..nbCustomers+2*nbVehicles;
set of int: DEPOT_NODES = nbCustomers+1..nbCustomers+2*nbVehicles;
set of int: START_DEPOT_NODES = nbCustomers+1..nbCustomers+nbVehicles;
set of int: END_DEPOT_NODES = nbCustomers+nbVehicles+1..nbCustomers+2*
    nbVehicles;
array[1..4, NODES, NODES] of int: distance;
array[NODES] of int: serviceTime = [5, 3, 6, 1, 3, 3, 0, 0, 0, 0];
array[1..4, NODES] of var NODES: successor;
array[1..4, NODES] of var NODES: predecessor;
array[NODES] of var VEHICLE: vehicle;
array[1..4, NODES] of var TIME: arrivalTime;
%%%%%%%%%%%%%%%%%%%%%%%%%
var 0..timeBudget*4*max(weights): objective;
%%%%%%%%%%%%%%%%%%%%%%%%%
distance = array3d(1..4, NODES, NODES, [0, 4, 5, 7, 9, 10, 4, 4, 4, 4, 4, 0, 6, 
    4, 5, 6, 3, 3, 3, 3, 5, 6, 0, 7, 9, 10, 3, 3, 3, 3, 7, 4, 7, 0, 2, 3, 4, 4, 
    4, 4, 9, 5, 9, 2, 0, 1, 6, 6, 6, 6, 10, 6, 10, 3, 1, 0, 7, 7, 7, 7, 4, 3, 
    3, 4, 6, 7, 0, 0, 0, 0, 4, 3, 3, 4, 6, 7, 0, 0, 0, 0, 4, 3, 3, 4, 6, 7, 0, 
    0, 0, 0, 4, 3, 3, 4, 6, 7, 0, 0, 0, 0, 0, 8, 5, 7, 9, 10, 4, 4, 4, 4, 8, 0, 
    6, 4, 5, 6, 5, 5, 5, 5, 5, 6, 0, 7, 9, 10, 3, 3, 3, 3, 7, 4, 7, 0, 2, 3, 6, 
    6, 6, 6, 9, 5, 9, 2, 0, 1, 6, 6, 6, 6, 10, 6, 10, 3, 1, 0, 7, 7, 7, 7, 4, 
    5, 3, 6, 6, 7, 0, 0, 0, 0, 4, 5, 3, 6, 6, 7, 0, 0, 0, 0, 4, 5, 3, 6, 6, 7, 
    0, 0, 0, 0, 4, 5, 3, 6, 6, 7, 0, 0, 0, 0, 0, 4, 5, 7, 9, 10, 4, 4, 4, 4, 4, 
    0, 6, 7, 5, 6, 3, 3, 3, 3, 5, 6, 0, 7, 9, 10, 9, 9, 9, 9, 7, 7, 7, 0, 2, 3, 
    4, 4, 4, 4, 9, 5, 9, 2, 0, 1, 6, 6, 6, 6, 10, 6, 10, 3, 1, 0, 7, 7, 7, 7, 
    4, 3, 9, 4, 6, 7, 0, 0, 0, 0, 4, 3, 9, 4, 6, 7, 0, 0, 0, 0, 4, 3, 9, 4, 6, 
    7, 0, 0, 0, 0, 4, 3, 9, 4, 6, 7, 0, 0, 0, 0, 0, 4, 5, 7, 9, 10, 4, 4, 4, 4, 
    4, 0, 6, 4, 5, 6, 3, 3, 3, 3, 5, 6, 0, 7, 9, 10, 6, 6, 6, 6, 7, 4, 7, 0, 5, 
    3, 7, 7, 7, 7, 9, 5, 9, 5, 0, 1, 6, 6, 6, 6, 10, 6, 10, 3, 1, 0, 7, 7, 7, 
    7, 4, 3, 6, 7, 6, 7, 0, 0, 0, 0, 4, 3, 6, 7, 6, 7, 0, 0, 0, 0, 4, 3, 6, 7, 
    6, 7, 0, 0, 0, 0, 4, 3, 6, 7, 6, 7, 0, 0, 0, 0]);
array[1..4] of int: weights = [3, 2, 2, 1];
constraint forall ( sc in 1..4 ) ( 
    forall ( n in nbCustomers+2..nbCustomers+nbVehicles ) ( 
        predecessor[sc, n]==n+nbVehicles-1 
    ) 
);
constraint forall ( sc in 1..4 ) ( 
    predecessor[sc, nbCustomers+1]==nbCustomers+2*nbVehicles 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in nbCustomers+nbVehicles+1..nbCustomers+2*nbVehicles-1 ) ( 
        successor[sc, n]==n-nbVehicles+1 
    ) 
);
constraint forall ( sc in 1..4 ) ( 
    successor[sc, nbCustomers+2*nbVehicles]==nbCustomers+1 
);
constraint forall ( n in START_DEPOT_NODES ) ( vehicle[n]==n-nbCustomers );
constraint forall ( n in END_DEPOT_NODES ) ( 
    vehicle[n]==n-nbCustomers-nbVehicles 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in START_DEPOT_NODES ) ( arrivalTime[sc, n]==0 ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in NODES ) ( successor[sc, predecessor[sc, n]]==n ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in NODES ) ( predecessor[sc, successor[sc, n]]==n ) 
);
constraint forall ( sc in 1..4 ) ( circuit ( i in NODES ) ( successor[sc, i] ) 
);
constraint forall ( sc in 1..4 ) ( 
    circuit ( i in NODES ) ( predecessor[sc, i] ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in CUSTOMER ) ( vehicle[predecessor[sc, n]]==vehicle[n] ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in CUSTOMER ) ( vehicle[successor[sc, n]]==vehicle[n] ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in CUSTOMER ) ( 
        arrivalTime[sc, n]+serviceTime[n]+distance[sc, n, successor[sc, n]]<=
    arrivalTime[sc, successor[sc, n]] 
    ) 
);
constraint forall ( sc in 1..4 ) ( 
    forall ( n in START_DEPOT_NODES ) ( 
        arrivalTime[sc, n]+serviceTime[n]+distance[sc, n, successor[sc, n]]<=
    arrivalTime[sc, successor[sc, n]] 
    ) 
);
%%%%%%%%%
constraint 
   objective = sum ( sc in 1..4 ) ( weights[sc]*max ( i in NODES ) ( arrivalTime[sc, i] ) );
solve :: seq_search([ int_search(vehicle, first_fail, indomain_min, complete),
                      int_search([successor[sc,j] | sc in 1..4, j in NODES], 
                                 first_fail, indomain_min, complete),
                      int_search([arrivalTime[sc,n] | sc in 1..4, n in NODES], 
                                 first_fail, indomain_min, complete)
                    ])                 
   minimize objective;
output [
    "successor = array2d(1..4, ", show(NODES), ", ", show(successor), ");\n",
    "predecessor = array2d(1..4, ", show(NODES), ", ", show(predecessor), ");\n",
    "vehicle = ", show(vehicle), ";\n",
    "arrivalTime = array2d(1..4, ", show(NODES), ", ", show(arrivalTime), ");\n",
    "objective = ", show(objective), ";\n"
];
