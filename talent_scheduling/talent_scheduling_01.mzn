% Talent Scheduling problem
% Peter J. Stuckey
% 14/12/2008

include "globals.mzn";

int: numActors; % number of actors
int: numScenes; % numer of scenes

%-- Types ---------------------------------------------------------------------
set of int: Actors = 1..numActors;
set of int: Scenes = 1..numScenes;

array[Actors,Scenes] of 0..1: ia; % actors for each scene
array[Scenes] of int: d; % duration of each scene
array[Actors] of int: c; % cost of each actor

array[Scenes,Actors] of bool: ab; % actors for each scene
ab = array2d(Scenes,Actors, [  ia[j,i] == 1 | i in Scenes, j in Actors] );

%-- Decision variables --------------------------------------------------------

array[Scenes] of var Scenes: s; % schedule of scenes

%-- Auxilliary variables ------------------------------------------------------

array[Scenes,Actors] of var bool: bef; % actors appearing before time t
array[Scenes,Actors] of var bool: aft; % actors appearing after time t
array[Scenes,Actors] of var bool: dur; % actors on set at time t
var int: cost;

%-- Constraints ---------------------------------------------------------------

constraint alldifferent(s); % each scene scheduled once

constraint
        forall (j in Actors)(bef[1,j] = false) /\   % no actors before time 1
        forall (j in Actors)(aft[numScenes,j] = false) /\  % no actors after end
	forall(t in 1..numScenes-1, j in Actors)(
               bef[t+1,j] = (ab[s[t],j] \/ bef[t,j])   /\ 
               aft[t,j] = (ab[s[t+1],j] \/ aft[t+1,j]) );

constraint 
	forall (j in Actors)( dur[1,j] = ab[s[1],j] ) /\   
        forall(t in 2..numScenes-1, j in Actors)( 
		 dur[t,j] = (bef[t+1,j] /\ aft[t-1,j])
	) /\
        forall (j in Actors)( dur[numScenes,j] = ab[s[numScenes],j]);


constraint cost = sum(i in Scenes)(
      	       	     sum(j in Actors)(
		     	   c[j] * d[s[i]] * bool2int(dur[i,j])
		     )
               );   

%-- Solving objective and solution output -------------------------------------

solve ::
      int_search(s, first_fail, indomain, complete)
      minimize cost;

output ["cost = ", show(cost), ";\ns = ", show(s),
%       ";\nbef = ", show(bef),
%       ";\naft = ", show(aft),
%       ";\ndur = ", show(dur),
%       ";\nab = ", show(ab),
       ";\n"
]; 
