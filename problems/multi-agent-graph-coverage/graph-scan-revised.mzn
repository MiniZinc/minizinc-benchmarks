% Use this editor as a MiniZinc scratch book
% Peter Schneider-Kamp's coverage problem
% create a library of examples

% Changes by the MiniZinc Challenge Organisers:
% - Add search annotation

enum EDGE;   % directed edge

array[EDGE] of int: length;
array[EDGE] of set of EDGE: succ; % which edges can be visited next from this edge
array[EDGE] of EDGE: reverse;     % the reverse of each edge

enum EDGEX = R(EDGE) ++ { end } ;

int: n; % number of drones
set of int: DRONE = 1..n;

int: makespan = sum(length)*(scanmultiplier+1) div n;
constraint trace("makespan = \(makespan);\n",true);
set of int: TIME = 0..makespan;

int: scanmultiplier;  % assume traversing the edge requires length time, while scanning multiplies this by this amount


array[DRONE,EDGEX] of var EDGEX: next;    % next edge after this one
array[DRONE,EDGEX] of var TIME: visit;    % when edge was started traversal
array[DRONE,EDGE] of var bool: scan;     % did this drone scan the edge 
array[DRONE,EDGE] of var int: traverse = 
array2d(DRONE,EDGE, [ (scan[d,e]*(scanmultiplier-1)+1)* length[e] 
                    | d in DRONE, e in EDGE]);  % time to traverse the edge


% The next is either a reachable edge, the same edge (meaning not used) or end
constraint forall(d in DRONE, e in EDGE)(next[d,R(e)] in { R(e2) | e2 in succ[e] } union { R(e), end });
constraint forall(d in DRONE)(next[d,end] in R(EDGE));
% FORCE END TO POINT AT THE START OF THE TOUR
include "globals.mzn";
constraint forall(d in DRONE)(alldifferent(next[d,..]));
%constraint forall(d in DRONE)(subcircuit(next[d,R(EDGE)]));

% scan edges must be traversed
constraint forall(d in DRONE, e in EDGE)(scan[d,e] -> next[d,R(e)] != R(e));

% visit time increases as we go
constraint forall(d in DRONE, e in EDGE)(if next[d,R(e)] == R(e) then visit[d,R(e)] = makespan endif);
constraint forall(d in DRONE, e in EDGE)(if next[d,R(e)] != R(e) 
                                         then visit[d,next[d,R(e)]] == visit[d,R(e)] + traverse[d,e] endif);
%constraint forall(d in DRONE, e in EDGE)(if forall(f in EDGE)(next[d,R(f)] != R(e)) then visit[d,R(e)] = 0 endif);
% REPLACEMENT
constraint forall(d in DRONE)(visit[d,next[d,end]] = 0);
constraint forall(d in DRONE, e in EDGE)(traverse[d,e]+traverse[d,reverse[e]] <= (scanmultiplier+1)*length[e]);
  constraint forall(d in DRONE, e in EDGE)(scan[d,e] \/ next[d,R(e)] != R(reverse[e]));
% IDEA ensure the first time an edge is traversed, its scanning

% does not hold - counterexample is Andorra 
%constraint forall(d in DRONE, e in EDGE)(if card(succ[e]) >= 2 then visit[d,R(e)] > 0 endif);

% IDEA if both directions have been taken, everything on the "other" side is unreachable (only for edges not part of bi-connected components)

% IDEA if an edge is out of reach (visit time+shortest distance greater than current value of makespan)
                                                                                 
% every edge is scanned
constraint forall(e in EDGE)(exists(d in DRONE)(scan[d,e] \/ scan[d,reverse[e]]));                                         
constraint forall(e in EDGE, d in DRONE)(not(scan[d,e] /\ scan[d,reverse[e]]));
%constraint forall(e in EDGE, d1 in DRONE, d2 in DRONE)(if (scan[d1,e] \/ scan[d1,reverse[e]]) /\ d2 != d1 then not(scan[d2,e] \/ scan[d2,reverse[e]]) endif);

var TIME: endtime;
constraint endtime = max(d in DRONE)(visit[d,end]);

solve :: seq_search([
  bool_search(scan, input_order, indomain_min),
  int_search([[visit[d, e], next[d, e]][i] | d in DRONE, e in EDGEX, i in 1..2], first_fail, indomain_min),
 ]) minimize endtime;
