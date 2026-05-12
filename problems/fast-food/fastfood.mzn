int: nr; % number of restaurants
set of int: Restaurant = 1..nr;
array[Restaurant] of string: name;

array[Restaurant] of int: k; % kilometre position
set of int: ks = { k[r] | r in Restaurant };
int: maxdist = max(ks);

% Pick one representative restaurant per position for cleaner output labels.
set of Restaurant: first = { min(r in Restaurant where k[r] == pos)(r) | pos in ks };

int: number_of_depots;
set of int: Depot = 1..number_of_depots;
array[Depot] of var 0..maxdist: p; % position of depot

% Candidate depot locations are restricted to observed restaurant positions.
constraint forall(d in Depot)(p[d] in ks);
% Order depot positions to break depot-index symmetry.
constraint forall(d in 1..number_of_depots-1)(p[d] < p[d+1]);

% Bounds for the objective variable help tighten the search domain.
int: obj_min = sum(r in Restaurant)(min(d in Depot)(lb(abs(p[d] - k[r]))));
int: obj_max = sum(r in Restaurant)(min(d in Depot)(ub(abs(p[d] - k[r]))));

% Sum of nearest-depot distances for all restaurants.
var obj_min .. obj_max: obj = sum(r in Restaurant)(min(d in Depot)(abs(p[d] - k[r])));

solve 
	:: int_search(p, input_order, indomain_min, complete)
	minimize obj;

output [ show(p), "\n", show(obj), "\n"]++
       [ if (fix(p[d]) == k[r]) then
       	    "depot(" ++ name[r] ++ "," ++ show(p[d]) ++ ").\n"
         else "" endif | d in Depot, r in first ];

