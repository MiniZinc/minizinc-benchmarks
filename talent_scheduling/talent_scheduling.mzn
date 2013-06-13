% Talent Scheduling problem
% Peter J. Stuckey
% 14/12/2008

include "globals.mzn";

int: numActors; % number of actors
int: numScenes; % numer of scenes

%-- Types ---------------------------------------------------------------------
set of int: Actors = 1..numActors;
set of int: Scenes = 1..numScenes;

array[Actors,Scenes] of 0..1: ia; % 01 definition of actors in scenes
array[Scenes] of set of Actors: a = 
     [ { j | j in Actors where ia[j,i] == 1} | i in Scenes] ; % actors for each scene
array[Scenes] of int: d; % duration of each scene
array[Actors] of int: c; % cost of each actor


%-- Decision variables --------------------------------------------------------

array[Scenes] of var Scenes: s; % schedule of scenes

%-- Auxilliary variables ------------------------------------------------------

array[Scenes] of var set of Actors: bef; % actors appearing before time t
array[Scenes] of var set of Actors: aft; % actors appearing after time t
array[Scenes] of var set of Actors: dur; % actors on set at time t

var int: cost;

%-- Constraints ---------------------------------------------------------------

constraint alldifferent(s); % each scene scheduled once

constraint
        bef[1] = {} /\       % no actors before time 1
        aft[numScenes] = {} /\       % no actors after time numScenes
	forall(t in 1..numScenes-1)(
               bef[t+1] = a[s[t]] union bef[t]   /\ 
               aft[t] = a[s[t+1]] union aft[t+1] );

constraint 
	dur[1] = a[s[1]] /\   
        forall(t in 2..numScenes-1)( 
		 dur[t] = bef[t+1] intersect aft[t]
	) /\
        dur[numScenes] = a[s[numScenes]];

constraint cost = sum(i in Scenes)(
      	       	     sum(j in Actors)(
		     	   c[j] * d[s[i]] * bool2int(j in dur[i])
		         )
                  );   

%-- symmetry breaking constraint
constraint s[1] < s[numScenes];

%-- Solving objective and solution output -------------------------------------

solve :: int_search(s, first_fail, indomain, complete)
      minimize cost;

output ["cost = ", show(cost), ";\ns = ", show(s), 
       ";\ndur = ", show(dur), 
       ";\nbef = ", show(bef), 
       ";\naft = ", show(aft),
       ";\na = ", show(a),
       ";\n"]; 
