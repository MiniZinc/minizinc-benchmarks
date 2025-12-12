% Adapted from https://github.com/Kurorororo/didp-models/blob/main/graph-clear/graph_clear_cp.py

include "globals.mzn";

int: n;

enum NODE = Node(1..n);

array [NODE] of int: node_weights;
array [NODE, NODE] of int: edge_weights;

int: m = count (i, j in NODE) (edge_weights[i, j] > 0);
enum EDGE = Edge(1..m);
any: edges = array1d(EDGE, [(i, j) | i, j in NODE where edge_weights[i, j] > 0]);

int: z_lb = 1;
int: c_block = sum(edge_weights);
int: z_ub = max(node_weights) + c_block;
int: c_sweep = max(i in NODE) (node_weights[i] + sum(j in NODE) (edge_weights[i, j] + edge_weights[j, i]));

array [NODE] of var NODE: var_t;
array [EDGE] of var NODE: var_l;
array [EDGE] of var NODE: var_u;
array [NODE] of var 1..c_sweep: var_s;
array [NODE] of var 0..c_block: var_b;
array [EDGE, NODE] of var bool: var_i;
var z_lb..z_ub: var_z;

var int: objective = var_z;
solve :: int_search(var_t, smallest, indomain_min) minimize objective;

constraint var_z = max (t in NODE) (var_s[t] + var_b[t]);

constraint forall (i, t in NODE) (
  if var_t[i] = t then
    var_s[t] = node_weights[i] + sum (j in NODE) (edge_weights[i, j] + edge_weights[j, i])
  endif
);

constraint all_different(var_t);

constraint forall (e in EDGE, edge = edges[e], i = edge.1, j = edge.2) (
  if var_t[i] < var_t[j] then var_l[e] = var_t[i] /\ var_u[e] = var_t[j] endif /\
  if var_t[j] < var_t[i] then var_l[e] = var_t[j] /\ var_u[e] = var_t[i] endif /\
  forall (t in NODE) (if var_l[e] <= t /\ var_u[e] >= t /\ var_t[i] != t /\ var_t[j] != t then var_i[e, t] endif)
);

constraint forall (t in NODE) (
  var_b[t] = sum(e in EDGE, edge = edges[e], i = edge.1, j = edge.2) (edge_weights[i, j] * var_i[e, t])
);
