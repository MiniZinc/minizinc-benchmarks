%
% gfd-schedule.mzn
%
% Scheduling problem:
%
%   Constraints:
%    * Items are grouped by its 'kind'.
%    * Items are processed by group using 'facility'.
%    * Items must be processed after 'producedDay'.
%    * Maximum number of processed-items/day is fixed.
%
%   Objective:
%     Items may be processed before 'deadLineDay'.
%     Minimize group. (minimize use of facility)
%

include "nvalue.mzn";
include "at_most.mzn";
include "cumulative.mzn";

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Parameters
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% how many items
int: N;

% how many facilities
int: F;

% max items per day
int: MaxItemsPerDay;

% max day of schedule
int: MaxDay;

% item names
array[1..N] of string: name;

% kind of items
array[1..N] of int: kind;

% which facility can be used to process item
array[1..N] of set of 1..F: facility;

% item must be tested after producedDay
array[1..N] of int: producedDay;

% item must be tested until deadLineDay
array[1..N] of int: deadLineDay;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% item -> group mapping
array[1..N] of var 1..N: assignedGroup;

% group -> facility mapping (0 if group number not used)
array[1..N] of var 0..F: groupFacility;

array[1..N] of var 0..MaxDay: groupProcessDay;

array[1..N] of var 1..MaxDay: itemProcessDay;

var 1..N: nGroups;

int: dlp_max = sum(i in 1..N)(MaxDay - deadLineDay[i]);
var 0..dlp_max: deadLinePenalty;

int: obj_min = lb(deadLinePenalty) * 100 + lb(nGroups);
int: obj_max = ub(deadLinePenalty) * 100 + ub(nGroups);
var obj_min..obj_max: objective;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint
	forall(i in 1..N) (
		itemProcessDay[i] = groupProcessDay[assignedGroup[i]]
	);

% one group contains only one kind of item
constraint
	forall(i, j in 1..N where i < j) (
		kind[i] != kind[j] -> assignedGroup[i] != assignedGroup[j]
	);

constraint
	forall(k in lb_array(kind)..ub_array(kind)) (
		let {
			int: base = card({ i | i in 1..N where kind[i] < k});
			int: size = card({ i | i in 1..N where kind[i] = k});

			% index set of items having same kind (may be assigned to same group)
			array[1..size] of int: giset = [i |i in 1..N where kind[i] == k];
		} in
		% define group number selection range
		forall(i in index_set(giset)) (
			base < assignedGroup[giset[i]] /\ assignedGroup[giset[i]] <= base + size
		)
	);

% set 0 if not used
constraint
	forall(g in 1..N) (
		exists(i in 1..N)(assignedGroup[i] = g) != true
		<-> (groupFacility[g] == 0 /\ groupProcessDay[g] == 0)
	);

% set group order
constraint symmetry_breaking_constraint(
	forall(k in lb_array(kind)..ub_array(kind)) (
		let {
			int: base = card({ i | i in 1..N where kind[i] < k});
			int: size = card({ i | i in 1..N where kind[i] = k});

			% index set of items having same kind (may be assigned to same group)
			array[1..size] of int: giset = [i |i in 1..N where kind[i] == k];
		} in
		% define group number selection range
		forall(i in index_set(giset)) (
			assignedGroup[giset[i]] <= base + i
		)
		/\
		% use group number from smaller to bigger
		forall(g, h in base+1..base+size where g < h) (
			groupFacility[g] == 0 -> groupFacility[h] = 0
		)
	)
);

% facility is assinged to group according to item's facility
constraint
	forall(i in 1..N) (
		groupFacility[assignedGroup[i]] in facility[i]
	);

function var int: groupUsesFacility(int: g, int: f) = (
	if (groupFacility[g] == f) then
	   1
	else
	   0
	endif
);

% facility must be used by group exclusively
constraint
	forall(i in 1..F) (
		 let {
		     array[1..N] of var 1..1 : oneDay;
		 } in
		 cumulative(groupProcessDay, oneDay,
		 	[groupUsesFacility(g, i) | g in 1..N], 1)
	);


% items must be assigned to facility after its producedDay
constraint
	forall(i in 1..N) (
		producedDay[i] < groupProcessDay[assignedGroup[i]]
	);

% items per day
constraint
	forall(d in 1..MaxDay) (
		at_most(MaxItemsPerDay, itemProcessDay, d)
	);

% penalty
function var int: itemDeadLinePenalty(int: i) = (
	if (itemProcessDay[i] <=  deadLineDay[i]) then
	   0
	else
	   itemProcessDay[i] - deadLineDay[i]
	endif
);

constraint
	deadLinePenalty = sum(i in 1..N) (itemDeadLinePenalty(i));

constraint nvalue(nGroups, assignedGroup);

constraint objective = deadLinePenalty * 100 + nGroups;

solve 
    :: seq_search([
        int_search(assignedGroup ++ groupFacility ++ groupProcessDay,
            first_fail, indomain_min, complete),
        int_search(itemProcessDay ++ [nGroups, deadLinePenalty, objective],
            first_fail, indomain_min, complete)
    ])
    minimize objective;

output [ "% item\t k, g, f, day\n" ]
	   ++ [ "% \(name[i])\t \(kind[i]), \(assignedGroup[i]), \(groupFacility[assignedGroup[i]]), \(itemProcessDay[i]) (\(producedDay[i]) - \(deadLineDay[i]))\n" | i in 1..N
	   ]
	   ++ [ "assignedGroup = \(assignedGroup);\n" ]
	   ++ [ "groupFacility = \(groupFacility);\n" ]
	   ++ [ "groupProcessDay = \(groupProcessDay);\n" ]
	   ++ ["objective = \(objective);\n"];
