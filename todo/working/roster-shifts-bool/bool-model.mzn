% Changes by the MiniZinc Challenge Organisers:
% - Disable constraint which was found to be incorrect

% Parameters
par int: n_shifts;
par int: n_employees;
par int: n_expertises;
array[EMPLOYEE] of par int: contract;
array[EMPLOYEE] of par set of EXPERTISE: employee_expertises;
array[SHIFT] of par EXPERTISE: req_expertise;
array[SHIFT] of par int: start_time;
array[SHIFT] of par int: stop_time;
par int: time_units_per_hour;
par set of int: SHIFT     = 1..n_shifts;
par set of int: EMPLOYEE  = 1..n_employees;
par set of int: EXPERTISE = 1..n_expertises;

% Validations
include "sort.mzn";
constraint assert(start_time=sort(start_time), "Start times should be sorted");

% Variables
array[EMPLOYEE, SHIFT] of var bool: assigned :: output;
array[EMPLOYEE] of var int: contract_diff = [ sum (s in SHIFT) (assigned[e, s]*(stop_time[s]-start_time[s])) - contract[e] | e in EMPLOYEE ];

% Functions
function bool: overlapping(SHIFT: s1, SHIFT: s2) = start_time[s1] < stop_time[s2] /\ start_time[s2] < stop_time[s1];
function set of SHIFT: shifts_in_period(int: start, int: stop) = { s | s in SHIFT where start_time[s] < stop /\ start < stop_time[s] };
function par set of SHIFT: overlapping_shifts_of(SHIFT: s) = { o | o in SHIFT where overlapping(o, s) };
function par bool: identical_shifts(SHIFT: s1, SHIFT: s2) = start_time[s1] = start_time[s2] /\ stop_time[s1] = stop_time[s2] /\ req_expertise[s1] = req_expertise[s2];
function par bool: identical_employees(EMPLOYEE: e1, EMPLOYEE: e2) = contract[e1] = contract[e2] /\ employee_expertises[e1] = employee_expertises[e2];

% Constraints
constraint forall (s in SHIFT) (sum (e in EMPLOYEE) (assigned[e, s]) <= 1); % No double assignments
constraint forall (s1, s2 in SHIFT where s1 < s2 /\ overlapping(s1, s2)) (forall (e in EMPLOYEE) (assigned[e, s1] + assigned[e, s2] <= 1)); % No overlapping assignments
constraint forall (e in EMPLOYEE, s in SHIFT where not (req_expertise[s] in employee_expertises[e])) (not assigned[e, s]); % Appropriate expertise required
constraint forall (e in EMPLOYEE where contract[e] > 0) (10 * sum (s in SHIFT) (assigned[e,s] * (stop_time[s] - start_time[s])) <= 13 * contract[e]); % Not allowed to work more than 130% of your contract

% Constraints -- redundant
% - Does not appear to be correct, since this would prevent two non-overlapping shifts being both assigned, if they both overlap with a middle shift
% constraint forall (s in SHIFT, e in EMPLOYEE) (sum (t in overlapping_shifts_of(s)) (assigned[e, t]) <= 1); % No overlapping assignments

% Constraints -- Symmetry-breaking
constraint symmetry_breaking_constraint(forall (s1, s2 in SHIFT where s1 < s2 /\ identical_shifts(s1, s2)) (sum (e in EMPLOYEE) (assigned[e, s2]) <= sum (e in EMPLOYEE) (assigned[e, s1])));

% Objective
var int: number_assigned_shifts = sum (e in EMPLOYEE, s in SHIFT) (assigned[e, s]);
var int: summed_abs_contract_diff = sum (e in EMPLOYEE) (abs(contract_diff[e]));
par int: W = 1 + max(max (e in EMPLOYEE) (contract[e]), max (s in SHIFT) (stop_time[s] - start_time[s])); % Weight factor for objective to be lexicographical
var int: objective = W*number_assigned_shifts - summed_abs_contract_diff;
solve :: search maximize objective;
ann: search = bool_search(assigned, input_order, indomain_max, complete);

output [
  "number_assigned_shifts = \(number_assigned_shifts);\n",
  "summed_abs_contract_diff = \(summed_abs_contract_diff);\n",
  "objective = \(objective);",
];
