% Monitor 1id Problem
int: n; % number of nodes
int: r; % number of routes   
int: b; % number of biconnected components with only one articulation point
array[1..r,1..2] of int: routes_ends; % set of routes, contains index of starting and ending nodes of routes
array[1..r] of set of int: routes; % representation of routes, contains the set of nodes crossed by each route
array[1..b] of set of int: bi_comp; % biconnected components with only one articulation point for redundant constraints
array[int] of int: leaf_nodes; % list of independant nodes that need to be monitors

array[1..n] of var bool:x; % monitors
array[1..r] of var bool:y; % measurement paths

% for a route to be a monitor path, its endpoints needs to be both monitors
constraint forall (path in 1..r) (y[path] <-> (x[routes_ends[path,1]] /\ x[routes_ends[path, 2]]));

% each node in the network needs to be covered by at least one measurement path
constraint forall (node in 1..n) (
  exists([y[path]| path in 1..r where (node in routes[path])]));

% each node needs to be 1-identifiable, i.e. it needs to be distinguishable from each other node
constraint forall (node_a in 1..n) (
              forall (node_b in node_a+1..n) (
                exists([y[path] | path in 1..r where ((node_a in routes[path]) /\ not (node_b in routes[path])) \/ (not (node_a in routes[path]) /\ (node_b in routes[path]))])));


% Redundant constraints

% if a node is not contain in any path where it isn't the endpoint, we can assume that it will be a monitor
constraint forall (node in leaf_nodes) (x[node]);

% each biconnected component with only one articulation point needs to contain at least one monitor to cover its nodes
constraint forall (comp in 1..b) (exists([x[node] | node in bi_comp[comp]]));

% the goal is to minimize the number of monitors
solve :: bool_search(x ++ y, input_order, indomain_min) minimize(sum(x));

output ["nb monitors = \(sum(x))\n",
        "solution : \([i | i in 1..n where x[i]])\n"];