include "count.mzn";

% Array containing the name of considered stations
% and related parameters / sets
array[int] of string: stations_name; 
int: nSTATIONS = length(stations_name);
set of int: STATIONS = 1..nSTATIONS;

% Array containing the name of considered lines
% and related parameters / sets
array[int] of string: line_names;
int: nLINES = length(line_names);
set of int: LINES = 1..nLINES;
array[STATIONS] of set of int: station_lines;

% List of available services per line within 
% the considered time horizon (i.e. sum of services 
% across all time blocks).
array[int] of int: service_line;
set of int: SERVICES = 1..length(service_line); 

% Service schedule. Required for the rolling time window approach.
array[SERVICES,STATIONS] of int: service_schedule;

% Maximum number of passengers allowed per service
int: MAX_PAX; 

% Passenger demand
array[int] of int: flat_pax;
int: nPASSENGERS = length(flat_pax) div 3;
array[1..nPASSENGERS, 1..3] of int: trips = array2d(1..nPASSENGERS, 1..3, flat_pax);

% Compatibility time window for services. This will be 
% [start_time_block - forward_tw, end_time_block + backward_tw)
int: forward_TW;
int: backward_TW;

% Variables
array[1..nPASSENGERS] of var SERVICES: p;
array[SERVICES,STATIONS] of var 0..MAX_PAX: pax;
int: obj_ub = nSTATIONS * length(service_line) * 10000;
var 0..obj_ub: objective;

% Execution parameters
int: objective_type;



% Constraint to ensure passengers are assigned to compatible services within the defined TW, 
% or to the next available service reaching their destination.
constraint forall(i in index_set(p)) ( p[i] in {s | s in SERVICES where 
                                                    service_schedule[s,trips[i,2]] > 0 /\
                                                    service_schedule[s,trips[i,3]] > 0 /\
                                                    service_line[s] in station_lines[trips[i,2]] intersect station_lines[trips[i,3]] /\
                                                    service_schedule[s,trips[i,2]] >= trips[i,1] - forward_TW /\
                                                    service_schedule[s,trips[i,2]] <= trips[i,1] + backward_TW}
                                               union
                                               {{s | s in SERVICES where 
                                                    service_schedule[s,trips[i,2]] > 0 /\
                                                    service_schedule[s,trips[i,3]] > 0 /\
                                                    service_line[s] in station_lines[trips[i,2]] intersect station_lines[trips[i,3]] /\
                                                    service_schedule[s,trips[i,2]] >= trips[i,1]}[1]});
                

% Constraint to compute the number of passengers onboard each service departing every station.
constraint forall(s in SERVICES) ( 
              forall(st in STATIONS) (
                 if service_schedule[s,st] == 0 then
                     pax[s,st] = 0
                 else
                     count([p[i] | i in 1..nPASSENGERS where trips[i,2] <= st /\ trips[i,3] > st],s,pax[s,st])
                 endif
              )
           );
           
% Constraint to compute the objective function
constraint if objective_type == 1 then
            objective = sum(i in SERVICES, j in STATIONS)(
                      if pax[i,j] < 265 then
                         0
                      elseif pax[i,j] < 529 then
                         10
                      elseif pax[i,j] < 663 then
                         100
                      elseif pax[i,j] < 800 then
                         1000
                      else
                         10000
                      endif)
           else
            objective = sum(i in SERVICES, j in STATIONS)(
                      if pax[i,j] < 265 then
                         0
                      elseif pax[i,j] < 529 then
                         (pax[i,j] - 264) * 1
                      elseif pax[i,j] < 663 then
                         (528 - 264) * 1 + (pax[i,j] - 528) * 5 
                      elseif pax[i,j] < 800 then
                         (528 - 264) * 1 + (662 - 528) * 5 + (pax[i,j] - 662) * 10
                      else
                         (528 - 264) * 1 + (662 - 528) * 5 + (799 - 662) * 10 + (pax[i,j] - 799) * 100
                      endif)
           endif;

solve :: int_search(p, input_order, indomain_min)
      minimize objective;

output [
    "p = \(p);\n",
    "objective = \(objective);\n"
];

%output [show(stations_name[i]) ++ if i == card(STATIONS) then "\n" else "\t" endif | i in STATIONS] ++
%       [show(pax[s,i]) ++ if i == card(STATIONS) then "\n" else "\t" endif | s in SERVICES, i in STATIONS] ++
%       ["---\n"] ++
%       ["Objective: " ++ show(objective)];

