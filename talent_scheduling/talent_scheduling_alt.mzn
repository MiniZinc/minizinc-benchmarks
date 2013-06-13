% originally for SOLVER by Paul Shaw
% modified by Barbara Smith
% converted to MiniZinc by Peter J. Stuckey
%
%

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

array[Scenes] of var Scenes: slot;  % inverse of scene permutation
array[Actors] of var Scenes: firstSlot; % first slot where actor appears
array[Actors] of var Scenes: lastSlot; % last slot where actor appears
array[Actors] of var int: wait; % onset time

var int: cost;

%-- Predicates ---------------------------------------------------------------

%-- Predicate to set up firstSlot and lastSlot

predicate firstlast(Actors: actor, 
                    array[Actors,Scenes] of 0..1: ia,
                    array[Scenes] of var Scenes: slot, 
	            var Scenes: first, 
                    var Scenes: last) = 
     let {
         int: n = card({ i | i in Scenes where ia[actor,i] == 1 }),
         array[1..n] of var Scenes: position = [ slot[i] | i in Scenes where ia[actor,i] == 1 ]
     } in
         first = min(position) /\
	 last = max(position) /\
	 last - first >= n - 1;




%-- Constraints ---------------------------------------------------------------

constraint inverse(s,slot);

constraint forall(j in Actors)(
	   	 firstlast(j, ia, slot, firstSlot[j], lastSlot[j])
		 );

constraint forall(j in Actors)(
	   	  wait[j] = sum(i in Scenes where ia[j,i] == 0)(
		       	       d[i] * bool2int(firstSlot[j] <= slot[i] /\
			                       slot[i] <= lastSlot[j])
			  ));

%-- Redundant Constraints -----------------------------------------------------

%% implied constraint from Barbara Smith: cost on waiting time
constraint forall(j in Actors)(
	   	  wait[j] >= lastSlot[j] - firstSlot[j] - 
		  	     card({ i | i in Scenes where ia[j,i] == 1 })
		  );

% implied constraints on ordering of scenes
constraint forall(i,j in Scenes where a[i] superset a[j])(
	   let {
	         set of Actors: diffn = a[i] diff a[j]
	   } in 
	     if (card(diffn) == 1) then
	     	forall(k in diffn)(
			 slot[j] < slot[i] -> firstSlot[k] > slot[j]
		)
             else if (card(diffn) == 2) then
	     	  forall(k,l in diffn where k < j)(
		  	 slot[j] < slot[i] -> (firstSlot[k] > slot[j] \/ firstSlot[l] > slot[j])
		  )
	     else
		true
	     endif endif
	  );

%-- calculating the objective function

constraint cost = sum(j in Actors)(
	   	  	sum(i in Scenes)(
		     	   c[j] * d[i] * ia[j,i] %% fixed cost
		        ) +
			c[j] * wait[j]
                  );   

%-- symmetry breaking constraint
constraint s[1] < s[numScenes];

%-- Solving objective and solution output -------------------------------------

solve :: int_search(s, first_fail, indomain, complete)
      minimize cost;

output ["cost = ", show(cost), ";\ns = ", show(s), 
       ";\nslot = ", show(slot), 
       ";\nfirstSlot = ", show(firstSlot), 
       ";\nlastSlot = ", show(lastSlot), 
       ";\nwait = ", show(wait),
       ";\na = ", show(a),
       ";\n"]; 
