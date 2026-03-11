%------------------------------------------------------------------------------%
% vrp.mzn
% Jakob Puchinger
% July 2009
% vim: ft=zinc ts=4 sw=4 et tw=0
%------------------------------------------------------------------------------%

    % The number of Nodes, Node 0 corresponds to the depot
int: N;
    % Vehicle capacity
int: Capacity;
    % Maximum number of vehicles
int: K = N;    
    % Demand at Node
array[1..N] of int: Demand;
    % Distances between the nodes
array[1..N+1, 1..N+1] of int: Distance;
    % Decision variables, is arc ij part of a route?
array[0..N, 0..N] of var 0..1: x;
    % Additional variables representing the load of vehicle after visiting
    % node i for subtour elimination
array[1..N] of var 0..Capacity: u;

    % Indegree constraints
constraint
    forall(j in 1..N)(
        sum(i in 0..N)(x[i, j]) = 1
    );
    
    % Outdegree constraints
constraint
    forall(i in 1..N)(
        sum(j in 0..N)(x[i, j]) = 1
    );

    % Indegree Depot
constraint
    sum(i in 0..N)(x[i, 0]) <= K;

    % Outdegree Depot
constraint
    sum(j in 0..N)(x[0, j]) <= K;

    % Subtour elimination (Miller, Tucker Zemlin)
constraint
    forall( i in 1..N, j in 1..N)(
        u[i] - u[j] + Capacity * x[i, j] <= Capacity - Demand[j]
    )
    /\ forall(i in 1..N)(
        Demand[i] <= u[i]
    );

int: obj_min = 0;
int: obj_max = sum(i, j in 0..N)(Distance[i+1, j+1]);

var obj_min..obj_max: objective =
    sum( i in 0..N, j in 0..N ) (Distance[i+1, j+1] * x[i, j]); 

solve 
    :: int_search(u ++ [x[i, j] | i in 1..N, j in 1..N],
        first_fail, indomain_min, complete) 
    minimize objective;

output [
    "x = ", show(x), ";\n",
    "objective = ", show(objective), ";\n"
];
