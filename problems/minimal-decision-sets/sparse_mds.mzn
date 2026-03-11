% Use this editor as a MiniZinc scratch book

int: n = 5; % max number of nodes
set of int: NODE = 1..n;
int: Lambda = I div 20; % number of misclassification worth one node

enum FEATURE;     % set of features
FEATURE: class;   % class is one feature

enum FEATUREX = anon_enum(card(FEATURE) + 1);
var FEATURE: tof(var FEATUREX: f) = to_enum(FEATURE,f);
var FEATUREX: tofx(var FEATURE: f) = to_enum(FEATUREX,f);
FEATUREX: dummy = max(FEATUREX);                   % dummy feature representing unused
FEATUREX: classx = to_enum(FEATUREX,class);                    % class feature

int: I; % number of items
set of int: ITEM = 1..I;

array[ITEM,FEATURE] of 0..1: db;   % database of 

array[NODE] of var bool: sign;        % information for the node is true or false
array[NODE] of var FEATUREX: feat;    % which features is discriminated on (class for leafs) or unused
array[NODE, ITEM] of var bool: valid; % this item is valid at this node
array[ITEM] of var bool: m;           % misclassified item

%% Auxilliary variables
set of int: NODE0 = 0..n;
array[NODE0] of var bool: leaf = array1d(NODE0,[ if j in NODE then feat[j] = classx else true endif | j in NODE0 ]);     % is the node a leaf node
array[NODE] of var bool: unused = [ feat[j] = dummy | j in NODE ];

var 1..n: k = n - sum(unused);  % number of used nodes

% leaf and unused constraints
constraint not leaf[1];
constraint leaf[n] \/ unused[n];
constraint forall(i in 2..n)(unused[i] -> unused[i-1] \/ leaf[i-1]);
constraint forall(i in 1..n-1)(unused[i] -> unused[i+1]);
constraint forall(i in 1..n)(k < i -> unused[i]);
constraint forall(i in NODE)(unused[i] -> not sign[i]);

% validity propagation
constraint forall(i in ITEM)(valid[1,i]);
constraint forall(j in 1..n-1, i in ITEM)
                 (valid[j+1,i] = (leaf[j] \/ (valid[j,i] /\ db[i,tof(feat[j])] = sign[j])));
                 
% correctness of leafs
constraint forall(i in ITEM, j in NODE)
                 (leaf[j] /\ valid[j,i] -> (db[i,class] = sign[j] \/ m[i]));
                 
% coverage: every item covered by one leaf                 
constraint forall(i in ITEM)
                 (m[i] \/ exists(j in NODE)(leaf[j] /\ valid[j,i]));
 
                                                 
% symmetry breaking: all features appear in increasing order in a decision set                 
%constraint symmetry_breaking(forall(j in 1..n-1)(leaf[j+1] \/ leaf[j] \/ unused[j] \/ feat[j+1] > feat[j]));   

% % symmetry breaking, first feature in each decision set in increasing order
%array[NODE] of var NODE0: previous_root = [ max([  k * leaf[k-1] | k in NODE where k < j] ++ [0]) | j in NODE ];
%constraint symmetry_breaking(forall(j in 2..n)(leaf[j-1] -> feat[j] >= feat[previous_root[j]]));   
         
         
% minimize number of 
var 0..I: misclassified = sum(m);         
var int: objective = misclassified + Lambda*k;
solve :: int_search([ if j = 1 then feat[i] else sign[i] endif | i in NODE, j in 1..2 ], input_order, indomain_min) 
          minimize objective;           

% output [show(feat)];

output [
  "objective = \(objective);\n",
  "sign = array1d(\(NODE), \(sign));\n",
  "valid = array2d(\(NODE), \(ITEM), \(valid));\n",
  "m = array1d(\(ITEM), \(m));\n",
  "feat = array1d(\(NODE), ["];
output ["to_enum(FEATUREX, \(feat[i]+0)), " | i in NODE];
output ["]);\n"];
                 
%output [ if i = 1 then show(j) ++ ": " else "" endif ++
%         if fix(valid[j,i]) then show(i) ++ " " else "" endif ++
%         if i = I then "\n" else "" endif    
%       | j in NODE, i in ITEM ];   
       
% output [ "k = \(k);\nleaf = \(leaf);\nunused = \(unused);\nsign = \(sign);\n" ];
% output [ "feat = ["] ++ [ if fix(unused[i]) then "--" else show(to_enum(FEATURE,feat[i])) endif ++ if i  < n then ", " else "];\n" endif | i in NODE ];
%%output [ "m = \(m);\n"];    

%output [ "previous_root = \(previous_root);\n" ];    
                                    