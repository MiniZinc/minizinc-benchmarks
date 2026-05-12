% train scheduling
enum STOP;                             % set of stops
STOP: dstop;                           % dummy stop
array[STOP] of int: minimal_wait;      % minimum wait time at station 
array[STOP,STOP] of opt 0..infinity: travel_time; % travel time from each stop to another <> if not possible
array[STOP] of int: platform;          % number of platforms at station
enum STYPE = { ORDINARY, HUB, TERMINUS };
array[STOP] of STYPE: stype;           % type of STOP
array[STOP] of int: skip_cost;         % cost to skip the station (per service)
enum LINE = { SING, DOUB, QUAD, NONE };
array[STOP,STOP] of LINE: line;        % line type between stops
                  
enum ROUTE;                            % a sequence of STOPs
int: max_route_length;                 % longest route in number of stops
set of int: STOPNO = 1..max_route_length;         
array[ROUTE] of STOPNO: rlength;       % length of route
array[ROUTE,STOPNO] of STOP: route;    % route definitions; 
   
enum SERVICE;                          % the set of services to be schedules                         
array[SERVICE] of ROUTE: sroute;       % the route for each service
int: makespan;                         % end of time considered;
set of int: TIME = 0..makespan;
TIME: min_sep;                         % min separation of services on the same line same direction
array[SERVICE] of TIME: service_start; % from when the service can start
array[SERVICE] of TIME: service_end;   % when the service ideally ends

enum ENGINE;                           % set of engines available
array[ENGINE] of STOP: start;          % start location for engines
enum SERVICEX = s(SERVICE) ++ e(ENGINE); 

%%%%%%%%%%% Assertions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(s in STOP)(assert(minimal_wait[s] >= 0, "Negative wait time for stop \(s)\n"));
constraint forall(s in STOP)(assert(skip_cost[s] >= 0, "Negative skip cost for stop \(s)\n"));
constraint forall(s in STOP where stype[s] != ORDINARY)
                 (assert(skip_cost[s] = 0, "Non-zero skip cost time for non-ORDINARY stop \(s)\n"));
constraint forall(s in STOP where s != dstop)(assert(platform[s] >= 1, "Non-positive platforms for stop \(s)\n"));
constraint assert(minimal_wait[dstop] = 0, "dummy stop must have min wait 0\n");
constraint assert(skip_cost[dstop] = 0, "dummy stop must have skip cost 0\n");
constraint assert(platform[dstop] = 0, "dummy stop must have 0 platforms\n");
%constraint assert(stype[dstop] = ORDINARY, "dummy stop must be ordinary\n");
constraint forall(s in STOP)(assert(travel_time[s,s] = 0, "Non zero self travel time for \(s)\n"));
constraint forall(s in STOP)(assert(travel_time[s,dstop] = 0 /\ travel_time[dstop,s] = 0 , 
                                   "Non zero travel time from dummy to stop \(s)\n"));
constraint assert(min_sep >= 0, "min_sep is negative\n");
constraint forall(s in SERVICE)(assert(service_end[s] >= service_start[s], "service \(s) start end time problem\n"));
constraint forall(s1, s2 in STOP where s1 <= s2)(assert(line[s1,s2] = line[s2,s1] , 
                                                 "Non symmetric line \((s1,s2))\n"));
%%%% line type agrees with travel time
constraint forall(st1, st2 in STOP)(assert((absent(travel_time[st1,st2]) \/ travel_time[st1,st2] = 0)
                                           <->line[st1,st2] = NONE, 
                                           "travel time (\(st1),\(st2)) doesnt agree with line type\n"));
%%%% route length agrees with dstops
constraint forall(r in ROUTE, s in STOPNO)
                 (assert(s > rlength[r] <-> route[r,s] = dstop,
                         "route length and route definition for route \(r) dont agree\n"));                     
%%%% each used leg appears in the traveltime/line type
constraint forall(r in ROUTE, s in 1..<rlength[r])
                 (assert(line[route[r,s],route[r,s+1]] != NONE, "Leg \(route[r,s])-\(route[r,s+1]) does not exist\n"));

%%%%%%%%%%% Decisions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

include "globals.mzn";

array[SERVICE,STOPNO] of var TIME: arrive;    % arrive time at each stop
array[SERVICE,STOPNO] of var TIME: depart;    % depart time at each stop
array[SERVICE,STOPNO] of var TIME: wait;      % wait time at each stop
array[SERVICE,STOPNO] of var bool: stopped;   % which stops are actually made                                                            
var 0..infinity: delay_obj;
var 0..infinity: skip_obj; 
array[SERVICE] of var ENGINE: engine;         % which engine is used for each service
array[SERVICE] of var SERVICEX: prev;         % previous service or engine

%%%%%%%%%%% STAGE A - schedule constraints 
include "globals.mzn";

%constraint forall(s in SERVICE, n in STOPNO)
%                 (stopped[s,n]);



% A service starts after its service start time
constraint forall(s in SERVICE)(arrive[s,1] >= service_start[s]);
% the departure time is at least the minimal_wait time for the stop after arrival
constraint forall(s in SERVICE, n in STOPNO)
                 (wait[s,n] = depart[s,n] - arrive[s,n]);
constraint forall(s in SERVICE, n in STOPNO)
                 (wait[s,n] >= stopped[s,n] * minimal_wait[route[sroute[s],n]]);
% the arrival time for the next stop is at least the travel time after the departure from previous stop                 
constraint forall(s in SERVICE, n in 1..< rlength[sroute[s]])
                 (arrive[s,n+1] >= depart[s,n] + travel_time[route[sroute[s],n],route[sroute[s],n+1]]);
% for dummy stops, just copy the last depart time                 
constraint forall(s in SERVICE, n in rlength[sroute[s]]..<max_route_length)
                 (arrive[s,n+1] = depart[s,n] /\ depart[s,n+1] = depart[s,n]);

                                
%%%%%%%%%%% STAGE B - stop constraints 
constraint forall(st in STOP where st != dstop)
                 (if card(ENGINE) > platform[st] then
                  cumulative( [ arrive[s,n] | s in SERVICE, n in STOPNO where route[sroute[s],n] = st ],
                              [ wait[s,n]| s in SERVICE, n in STOPNO where route[sroute[s],n] = st ],
                              [ 1 | s in SERVICE, n in STOPNO where route[sroute[s],n] = st ],
                              platform[st])
                  endif);
  
                                                      
%%%%%%%%%%% STAGE C - objective constraints 
constraint delay_obj = sum(s in SERVICE)(abs(depart[s,max_route_length] - service_end[s]));
                                                           
 
constraint forall(s in SERVICE, n in STOPNO)
                 (if stype[route[sroute[s],n]] != ORDINARY then stopped[s,n] endif);                             
                 
constraint skip_obj = sum(s in SERVICE, n in STOPNO)
                         (skip_cost[route[sroute[s],n]]*(1-stopped[s,n]));                         
                         
var 0..sum(skip_cost) + card(SERVICE) * makespan: objective = delay_obj + skip_obj;
% objective minimizes combined lateness and stop-skipping penalties.
solve :: seq_search([
   int_search(array1d(arrive) ++ array1d(depart) ++ array1d(wait), smallest, indomain_min),
   bool_search(stopped, smallest, indomain_min),
   int_search(array1d(prev), first_fail, indomain_min),
]) minimize objective;

%%%%%%%%%%%%%%% STAGE C -- dominance
% always start the earlier service first
% constraint forall(s1, s2 in SERVICE where s1 != s2 /\ sroute[s1] = sroute[s2] 
%                   /\ service_start[s1] <= service_start[s2] /\ service_end[s1] <= service_end[s2] 
%                   /\ (service_start[s1] < service_start[s2] \/ service_end[s1] < service_end[s2] \/ s1 < s2))
%                  (arrive[s1,1] <= arrive[s2,1]);
% constraint forall(s in SERVICE, n in STOPNO)
%                  (if stype[route[sroute[s],n]] = ORDINARY /\ skip_cost[route[sroute[s],n]] = 0 then
%                      stopped[s,n] = false
%                   endif);


%%%%%%%%%%%%%%% STAGE D -- engine assignment
%% if the previous assignment is an engine the start location of the service and engine must agree
constraint forall(s in SERVICE)(prev[s] in e(ENGINE) -> route[sroute[s],1] = start[e^-1(prev[s])]); 
%% engine of the train is the given engine or engine of previous routs               
constraint forall(s in SERVICE)(engine[s] = if prev[s] in e(ENGINE) then e^-1(prev[s])
                                            else engine[s^-1(prev[s])] endif);                
%% engine transfer from same location                                                   
constraint forall(s in SERVICE)(if prev[s] in s(SERVICE) then 
                                   let { var SERVICE: sp = s^-1(prev[s]); } in
                                   route[sroute[s],1] = route[sroute[sp],rlength[sroute[sp]]]
                                endif);                
%% engine implies time precedence
constraint forall(s in SERVICE)(if prev[s] in s(SERVICE) then 
                                   let { var SERVICE: sp = s^-1(prev[s]); } in
                                   arrive[s,1] >= depart[sp,rlength[sroute[sp]]]
                                endif);                
constraint alldifferent(prev);

%%%%%%%%%%%%%%% STAGE D -- dominance constraints
% constraint forall(e1, e2 in ENGINE where e1 < e2 /\ start[e1] = start[e2])
%                  (forall(s1, s2 in SERVICE where s1 != s2)
%                         (prev[s1] = e(e1) /\ prev[s2] = e(e2) -> s1 < s2));



%%%%%%%%%%%%%%% STAGE E -- double track segments constraints

constraint forall(st1, st2 in STOP where st1 < st2 /\ line[st1,st2] = DOUB)
                 (let { array[int] of SERVICE: serviceleft = [ s | s in SERVICE where 
                                        exists(n in 1..rlength[sroute[s]]-1)
                                        (route[sroute[s],n] = st1 /\ route[sroute[s],n+1] = st2) ]; 
                        array[int] of STOPNO: stopleft = [ n | s in SERVICE, n in 1..rlength[sroute[s]]-1 where
                                        (route[sroute[s],n] = st1 /\ route[sroute[s],n+1] = st2) ];                 
                        array[int] of SERVICE: serviceright = [ s | s in SERVICE where 
                                        exists(n in 1..rlength[sroute[s]]-1)
                                        (route[sroute[s],n] = st2 /\ route[sroute[s],n+1] = st1) ]; 
                        array[int] of STOPNO: stopright = [ n | s in SERVICE, n in 1..rlength[sroute[s]]-1 where
                                        (route[sroute[s],n] = st2 /\ route[sroute[s],n+1] = st1) ]; 
                   } in              
                   if card(ENGINE) > 1 /\ length(serviceleft) > 1 then
                      trace("Double track L \(st1)-\(st2):\n",
                      disjunctive([ depart[serviceleft[i],stopleft[i]] | i in index_set(serviceleft) ],
                                  [ min_sep | i in index_set(serviceleft) ]) /\
                      forall(i, j in index_set(serviceleft) where i < j)
                         (depart[serviceleft[i],stopleft[i]] < depart[serviceleft[j],stopleft[j]] <->
                          arrive[serviceleft[i],stopleft[i]+1] + min_sep <= arrive[serviceleft[j],stopleft[j]+1])
                      )
                   endif /\
                   if card(ENGINE) > 1 /\ length(serviceright) > 1 then          
                      trace("Double track R \(st1)-\(st2):\n",
                      disjunctive([ depart[serviceright[i],stopright[i]] | i in index_set(serviceright) ],
                                  [ min_sep | i in index_set(serviceright) ]) /\
                      forall(i, j in index_set(serviceright) where i < j)
                         (depart[serviceright[i],stopright[i]] < depart[serviceright[j],stopright[j]] <->
                          arrive[serviceright[i],stopright[i]+1] + min_sep <= arrive[serviceright[j],stopright[j]+1])
                      )
                   endif
                );           


%%%%%%%%%%%%%%% STAGE F -- single track segments constraints


constraint forall(st1, st2 in STOP where st1 < st2 /\ line[st1,st2] = SING)
                 (let { array[int] of SERVICE: serviceleft = [ s | s in SERVICE where 
                                        exists(n in 1..rlength[sroute[s]]-1)
                                        (route[sroute[s],n] = st1 /\ route[sroute[s],n+1] = st2) ]; 
                        array[int] of STOPNO: stopleft = [ n | s in SERVICE, n in 1..rlength[sroute[s]]-1 where
                                        (route[sroute[s],n] = st1 /\ route[sroute[s],n+1] = st2) ]; 
                        int: lefttrains = length(serviceleft);                
                        array[int] of SERVICE: serviceright = [ s | s in SERVICE where 
                                        exists(n in 1..rlength[sroute[s]]-1)
                                        (route[sroute[s],n] = st2 /\ route[sroute[s],n+1] = st1) ]; 
                        array[int] of STOPNO: stopright = [ n | s in SERVICE, n in 1..rlength[sroute[s]]-1 where
                                        (route[sroute[s],n] = st2 /\ route[sroute[s],n+1] = st1) ]; 
                        int: righttrains = length(serviceright);
                        set of int: LEFT = 1..lefttrains;
                        set of int: RIGHT = lefttrains+1..lefttrains+righttrains;
                        set of int: LocalSERVICES = 1..lefttrains+righttrains;                
                        set of int: ExtraSERVICES = 0..lefttrains+righttrains;                
                        array[LocalSERVICES] of SERVICE: allserv = serviceleft ++ serviceright;
                        array[LocalSERVICES] of STOPNO:  allstop = stopleft ++ stopright; 
                 } in
                 if card(ENGINE) > 1 /\ length(allserv) > 1 then
                 trace("Single track \(st1)-\(st2):\n",
                        let { array[ExtraSERVICES] of var ExtraSERVICES: next; } in                
                        alldifferent(next) /\
                        forall(i in LEFT)
                              (if next[i] in LEFT then
                                  depart[allserv[next[i]],allstop[next[i]]] >= 
                                  min_sep + depart[allserv[i],allstop[i]]
                               elseif next[i] in RIGHT then
                                  depart[allserv[next[i]],allstop[next[i]]] >= 
                                  arrive[allserv[i],allstop[i]+1] 
                               else true endif) /\
                        forall(i in RIGHT)
                              (if next[i] in LEFT then
                                  depart[allserv[next[i]],allstop[next[i]]] >= 
                                  arrive[allserv[i],allstop[i]+1]          
                               elseif next[i] in RIGHT then
                                  depart[allserv[next[i]],allstop[next[i]]] >= 
                                  min_sep + depart[allserv[i],allstop[i]]
                               else true endif)
                   )
                 endif
                 );
