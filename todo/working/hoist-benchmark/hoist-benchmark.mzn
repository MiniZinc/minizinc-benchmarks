%
% Hoist scheduling model - M hoists 1 track
%
%
% Note: this file differs slightly from the file released at:
% https://doi.org/10.4121/uuid:211d5c86-ee65-455c-a8ab-9265aab1e289
%
% because the CPAIOR'20 reviewers observed that constraint:
%
%   constraint forall(i in 1..N)((r[i])*B[i] <= (r[i-1]+f(i-1))) ; %-20)) ;   % Hoists at same tank - add delays while hoists go up and down
%
% should be replaced by constraint:
%
%   constraint forall(i in 1..N)(r[i] <= r[i-1]+f(i-1) + p_ub*(Capacity-B[i])) ;
%
% to handle the case of non-boolean B's;
% this is used in the Constraints journal article, and in this file.
%
% Second, this file separates constraints (1) and (2) for ease of exposition.
%
% Third, this file also contains additional comments.
%
%
% accompanies CPAIOR 2020 abstract "A New Constraint Programming Model and Solving for the Cyclic Hoist Scheduling Problem", and Constraints journal article of the same title
%
% Copyright (c) 2020 M. Wallace and N. Yorke-Smith
% contact: n.yorke-smith@tudelft.nl
% released under CC BY-NC-SA license (https://creativecommons.org/licenses/by-nc-sa/4.0/)
%

include "globals.mzn" ;
%include "PU.dzn" ;
%include "B01.dzn" ;
%include "B02.dzn" ;


%%% parameters %%%

% Used so the user interface presents choices in this sequence:
int: Multiplier; 
int: Hoists;
int: Capacity;

int: J;  % Number of simult. jobs
int: Ninner;  %  Number of tanks
int: Tinner = Ninner+1;  % Number of treatments
int: N = Multiplier*Ninner ;

array [1..Ninner] of int: tmin ;  % Minimum time for job in each tank
array [1..Ninner] of int: tmax ;  % Maximum time for job in each tank
array [1..Tinner,0..Ninner] of int: e ;  % Empty travel time for hoist between tanks
array [0..Ninner] of int: f ;  % Travel time for job in hoist from each tank to its successor

int: INF = 9999 ;  % Infinity


%%% variables %%%

array[0..N] of var 0..p_ub: r;  % Removal time from each tank 
constraint forall(i in 0..N)( r[i] <= objective );

var p_lb..p_ub: objective;  % Cycle period
array [0..N] of var 1..Hoists: hoist ;  % Which hoist removes job from each tank
constraint symmetry_breaking_constraint(hoist[0]=1) ;  % Symmetry breaking constraint


%%% constraints %%%

array [1..N] of var 0..Capacity:B ;
constraint sum(B) <=J ;

constraint forall(i in 1..N)(r[i]+objective*B[i] >= r[i-1]+f(i-1)+tmin(i)) ;
constraint forall(i in 1..N)(r[i]+objective*B[i] <= r[i-1]+f(i-1)+tmax(i)) ;

constraint objective >= r[N]+f(N) ;
constraint r[0] = 0 ; 

% Added from the other model - assumes going direct to another tank is the shortest path!
% (1) If higher numbered hoist only removes from higher numbered tanks there can be no clash
% except as dealt with in constraint (3).
% In case higher numbered hoist removes from lower number tank, ensure the times are not overlapping
constraint forall(i in 1..N,j in 0..i-1)(hoist[i] > hoist[j] \/
              r[i]+f(i)+e(i+1,j)<=r[j]   \/   
              r[j]+f(j)+e(j+1,i)<=r[i] 
           );     
 
% (2) If hoist action goes over cycle boundary ensure it concludes before the next action                              
constraint forall(i in 1..N, j in 0..i-1 )(hoist[i] > hoist[j] \/
              ( r[i]+f(i)+e(i+1,j) <= r[j]+objective /\
                r[j]+f(j)+e(j+1,i) <= r[i]+objective
	      )
	   ); 

 % (3) Hoists at same tank - add delays while hoists go up and down                                        
constraint forall(i in 1..N)(r[i] <= r[i-1]+f(i-1)+p_ub*(Capacity-B[i])) ; %-20)) ;   


%%% bounds %%%
function int: next(int:k) =  (if k=N then 0 else tmin(k+1) endif) ;
int: p_lb =  sum(k in 1..N)(f(k)+
                            min([next(k)]++[e(k+1,j)|j in 0..N where j != k+1])) div Hoists;
int: p_ub = sum([reverse(sort([tmin(k)+f(k)|k in 1..N]))[k]|k in 1..N div Hoists]) ;


%%% solve %%%
solve   ::    seq_search([
                             int_search(r++[objective],input_order,indomain_min),
                             int_search(hoist,input_order,indomain_min),
                             int_search(B,first_fail,indomain_min)])  
        minimize objective ;


%%% output %%%
% output ["multiplier ", show(Multiplier), "\n"] ++ 
%        ["hoists ", show(hoist), "\n"] ++
%        ["removal times ", show(r), "\n"] ++
%        ["period ", show(p)] ++
%        ["\njobs ", show(sum(B))] ;
output [
  "r = array1d(0..\(N), \(r));\n",
  "objective = \(objective);\n",
  "hoist = array1d(0..\(N), \(hoist));\n",
];

%%% helper predicates for large instances (Multiplier>1) %%%

% This is the core function used by tmin, tmax, f and even e
% It is "x mod Ninner", adjusting "mod" to handle 1..Ninner instead of 0..Ninner-1
function int:multtank(int:x) =
    ((x-1) mod Ninner)+1 ;
 
% The standard mapping applies to tmin and tmax      
function int: tmin(int: i) =
    let { int: ic = multtank(i)
    }      in
    tmin[ic];
function int: tmax(int: i) =
    let { int: ic = multtank(i)
      } in    
     tmax[ic];
        
 % e is different because it is e(1..Tinner,0..Ninner)  
 % This version handles the extra time for moves from the m1th copy of tank i to the m2th copy of tank j
 function int: e(int: i, int:j)  =
    let { 
            int: ic = multempty(i),
            int: jc =  mult2empty(j),
            int: cyclei = cycleempty(i),
            int: cyclej = cycle2empty(j)           
         }
    in         5*abs(cyclei-cyclej) + e[ic,jc]; 
% This is the standard mapping extended to handle  e(y,N+1)
function int: multempty(int:x) =
    if    x=N+1 then Tinner
    else   multtank(x) endif ;
% This is the standard mapping extended to handle e(0,y)
function int: mult2empty(int:x) =
   if x=0 then 0 
    else multtank(x) endif ;  
% This calculates which copy, of the original Ninner tanks, x belongs to
function int: cycleempty(int:x) =
    if x=N+1 then Multiplier-1
    else (x-1) div Ninner endif;    
% This calculates which copy x belongs to  
function int: cycle2empty(int:x) =
   if x=0 then 0
   else (x-1) div Ninner endif;

% f is almost the same, except that it includes tank 0    
% This is the standard mapping extended to handle x=0
function int: f(int: i) =
    let { int: ic = mult2empty(i) } 
    in
    f[ic] ;      
