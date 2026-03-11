%------------------------------------------------------------------------------%
% Steiner Tree Problem
%   
%   Find a tree in a graph containing all the "terminal" nodes and minimize its 
%   weights.
%
% Submitter: Diege de Una
%
% Modified by MiniZinc team:
%   - Beautification of code
%   - Merging different model files into one.
%
%------------------------------------------------------------------------------%
% Includes

%------------------------------------------------------------------------------%
% Parameters

int: nbV;   % The number of nodes in the graph
int: nbE;   % The number of edges in the graph
int: nbT;   % The number of terminal nodes in the graph

set of int: nodes = 1..nbV;
set of int: edges = 1..nbE;
set of int: terms = 1..nbT;

set of int: terminals;

array [edges] of int: ws;   % The weights of edges

array [nodes,edges] of bool: adj;
array [edges,nodes] of bool: endnodes;

%------------------------------------------------------------------------------%
% Variables

array [nodes] of var bool: vs;  % Whether a node is part of the tree
array [edges] of var bool: es;  % Whether a edge is part of the tree
var nodes: root;                % Whichever node is the tree root
var 0..sum(ws): objective;      % The objective variable

%------------------------------------------------------------------------------%
% Predicates (Note that they will appear in a future MiniZinc release without 
% the prefix "my_"!)

    % Constrains the set of edges "es" of a given undirected graph to be a 
    % weighted spanning tree of weight "K"
predicate my_steiner(
    int: N,                         % The Number of nodes
    int: E,                         % The number of edges
    array[int] of int: from,        %
    array[int] of int: to,          % 
    array[int] of int: w,           % The weight of each edge in the given graph
    var int: root,                  % The tree root
    array[int] of var bool: ns,     % Whether a node is in the subgraph
    array[int] of var bool: es,     % Whether an edge is in the subgraph
    var int: K                      % The weight of the tree
) =
    assert(index_set(from) = 1..E,"steiner: index set of from must be 1..\(E)") /\
    assert(index_set(to) = 1..E,"steiner: index set of to must be 1..\(E)") /\
    assert(index_set(ns) = 1..N,"steiner: index set of ns must be 1..\(N)") /\
    assert(index_set(es) = 1..E,"steiner: index set of es must be 1..\(E)") /\
    assert(index_set(w) = 1..E,"steiner: index set of w must be 1..\(E)") /\
    if forall(n in 1..N)(is_fixed(ns[n]) /\ fix(ns[n])) then
        my_fzn_wst(N,E,from,to,w,root,es,K)
    else
        my_fzn_steiner(N, E, from, to, w, root, ns, es, K)
    endif;

predicate my_fzn_wst(
    int: N, 
    int: E, 
    array[int] of int: from, 
    array[int] of int: to, 
    array[int] of int: w,
    var int: r,
    array[int] of var bool: es, 
    var int: K
) = let { 
        array[1..N] of bool: ns = [true | n in 1..N]; 
    } in (
        my_fzn_tree(N,E,from,to,r,ns,es)
    /\  K = sum(e in 1..E)(es[e]*w[e])
    );

predicate my_fzn_tree(
    int: N, 
    int: E, 
    array[int] of int: from, 
    array[int] of int: to,
    var int: r, 
    array[int] of var bool: ns, 
    array[int] of var bool: es
) = let {
        array[1..2*E] of int: dfrom = from ++ to;
        array[1..2*E] of int: dto   = to ++ from;
        array[1..2*E] of var bool: des;
    } in (
        % ensure that the directed edges selected agree with undirected edges
        forall(e in 1..E)(es[e] <-> (des[e] \/ des[e+E]))
        % duplicate the edges so that the we can use directed graph reachability
    /\  my_fzn_dtree(N,2*E,dfrom,dto,r,ns,des)
    );

predicate my_fzn_dtree(
    int: N, 
    int: E, 
    array[int] of int: from, 
    array[int] of int: to,
    var int: r, 
    array[int] of var bool: ns, 
    array[int] of var bool: es
) = let {
        set of int: NODE = 1..N;
        set of int: EDGE = 1..E;
        array[NODE] of var 0..N-1: dist; /* distance from root */
        array[NODE] of var 0..N: parent; /* parent */
    } in (
        % the root must be chosen
        ns[r]   
        % root is at distance 0
    /\  dist[r] = 0 
        % nonselected nodes have parent 0
    /\  forall(n in NODE)( not ns[n] -> parent[n] <= 0 )
        % as does the root
    /\  parent[r] <= 0
        % nonselected nodes have distance 0
    /\  forall(n in NODE)( not ns[n] -> dist[n] = 0 )
        % each in node except root must have a parent
    /\  forall(n in NODE)( ns[n] -> (n = r \/ parent[n] > 0) )
        % each node with a parent then parent is in
    /\  forall(n in NODE)( parent[n] > 0 -> (ns[n] /\ ns[parent[n]]) ) 
        % each node with a parent is one more than its parent
    /\  forall(n in NODE)( parent[n] > 0 -> dist[n] = dist[parent[n]] + 1 )
        % each node with a parent must have that edge in
    /\  forall(n in NODE)(
            parent[n] > 0 -> 
                exists(e in EDGE)(es[e] /\ from[e] = parent[n] /\ to[e] = n)
        ) 
        % each edge must be part of the parent relation
    /\  forall(e in EDGE)( es[e] -> parent[to[e]] = from[e] )
        % redundant relationship of trees
    /\  sum(e in EDGE)(es[e]) = sum(n in NODE)(ns[n]) - 1
    /\  my_fzn_subgraph(N,E,from,to,ns,es)
);

predicate my_fzn_subgraph(
    int: N, 
    int: E, 
    array[int] of int: from, 
    array[int] of int: to,
    array[int] of var bool: ns, 
    array[int] of var bool: es
) = forall(e in 1..E)(
        (es[e] -> ns[from[e]]) 
    /\  (es[e] -> ns[  to[e]])
    );

predicate my_fzn_steiner(
    int: N, 
    int: E, 
    array[int] of int: from, 
    array[int] of int: to, 
    array[int] of int: w,
    var int: r,
    array[int] of var bool: ns, 
    array[int] of var bool: es, 
    var int: K
) = (
        my_fzn_tree(N,E,from,to,r,ns,es)
    /\  K = sum(e in 1..E)(es[e]*w[e])
    );

%------------------------------------------------------------------------------%
% Constraints

    % All terminal nodes must be part of the tree
    %
constraint forall(i in index_set(terminals))(
    vs[terminals[i]] == true
);

    % The objective value is the sum of the edge weights in the tree
    %
constraint redundant_constraint(
    objective = sum(i in edges)(bool2int(es[i]) * ws[i])
);

    % The number of edges in the tree is one less than number of the nodes.
    % Thus, it enforces that all nodes are connected to each other.
constraint redundant_constraint(
    sum(i in edges)(bool2int(es[i])) = sum(i in nodes)(bool2int(vs[i])) - 1
);

array [edges] of set of nodes: pairs = [ { n | n in nodes where endnodes[e,n]} | e in edges];
array [edges] of int: from = [ min(pairs[e]) | e in edges];
array [edges] of int: to   = [ max(pairs[e]) | e in edges];

constraint my_steiner(nbV, nbE, from, to, ws, root, vs, es, objective);

%------------------------------------------------------------------------------%
% Search and solve item

array [int] of int: es_search_idx;
array [int] of int: vs_search_idx;

solve 
    :: seq_search([
        int_search([es[i] | i in es_search_idx] ++ [vs[i] | i in vs_search_idx], input_order, indomain_min),
        int_search([root], input_order, indomain_min)
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "root = \(root);\n",
    "vs = \(vs);\n",
    "es = \(es);\n",
    "objective = \(objective);\n"
];

%------------------------------------------------------------------------------%

