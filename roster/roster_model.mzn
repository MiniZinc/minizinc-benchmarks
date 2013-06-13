% NOTE: the formulation of this problem that was used in the 2009
% MiniZinc challenge is in the file roster_model.old.  (That formulation
% is not compatible with MiniZinc 1.1 and above.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  FIT3022 
%  Assignment 1
%  Rostering Problem
%  Example Solution
%  6th May 2008
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This model should be paired with a data file, viz.
%    mzn_run(chicroster,data_A, fzn_ic)

% An example data file data_A is as follows:
    % reqt = [3,2,1,0,1,1,5, 
    %         1,0,1,0,1,2,0,
    %         1,2,0,1,1,1,0,
    %         0,1,2,2,2,1,0,
    %         0,0,1,2,0,0,0] ;
    %
    % weeks = 5 ;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Model
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Import predicates 'exactly', at_most', 'at_least' 
% which are defined in "globals.mzn"
include "globals.mzn" ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Parameters
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% "weeks" and "reqt" are imported from the data file.
% "flatsize" is a constant computed from the parameter "weeks", which is used
% in the model.
%
int: weeks ;
int: flatsize = 7 * weeks ;
array [1..5,1..7] of int: reqt ;
int: minobj;

% The following parameters aid readability of the model.
%
int:Rest=1;
int:Morn=2;
int:Day=3;
int:Eve=4;
int:Joker=5;

% The following two variables will hold the costs due to violated soft
% constraints.
%
var 0..flatsize: evemorn ;
var 0..flatsize: isolated ;

var 0..2*flatsize: objective = evemorn + isolated;

% The roster is an array of decision variables: each variable has domain 1..5
% representing possible shifts Rest,Morn,Day,Eve or Joker roster is a
% two-dimensional array with a row for each week
array [1..weeks,1..7] of var 1..5: roster; 

% flatroster is a one-dimensional array, which will contain exactly the same set of variables
array [1..flatsize] of var 1..5: flatroster ;
array [1..flatsize+6] of var 1..5: longflatroster ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint objective >= minobj;

constraint
    forall (d in 1..6) (longflatroster[flatsize+d] = flatroster[d]); 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Hard Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Roster Flat-Roster constraint
%
% Description:
% This constraint ensures that roster and flatroster contain the same set of
% variables.  The first seven variables in flatroster correspond to the first
% row (week) in roster.  The 8th to the 14th variables in flatroster correspond
% to the second row in roster, etc.  The total number of variables is the
% number of weeks times 7.
%
% Example violation:
% This constraint is violated if a variable in flatroster is different from the corresponding
% variable in roster, e.g.
%
%     flatroster = [1,2,2,2,2,2,2,2,2,2,2,2,2,2]
%     roster     = [2,2,2,2,2,2,2,
%                   2,2,2,2,2,2,2]
%
% The first day of week one is different in flatroster and roster
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint 
    forall (w in 1..weeks, d in 1..7) (flatroster[7*(w-1)+d] = roster[w,d]) ; %:: defines_var(roster) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Requirement Constraint  
%
% Description:
% The roster shifts must meet the requirement specified in the data
% Each day of the week, the sum of the sifts of each type must match the 
% required number for the given shift type on the given day of the week
%
% Example violation:
%  
%  %         M T W T F S S
   % reqt = [0,0,0,0,0,2,2, 
   %         1,1,0,1,1,0,0,
   %         1,1,0,1,1,0,0,
   %         0,0,2,0,0,0,0,
   %         0,0,0,0,0,0,0] ;
   %
   % weeks = 2 ;
%  
% 
%          
%	roster = [3,2,4,2,2,1,1,  
%                 3,3,4,3,3,1,1]     
%  This solution does not match the requirement for Monday 
%  (two Day shifts instead of a Morning and a Day shift).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint 
    forall (shift in 1..5)
            (forall (day in 1..7) 
                    (exactly(reqt[shift,day],[roster[week,day] | week in 1..weeks],shift))
            );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Enough Rest Constraint
%
% Description:
% Ensure that in any sequence of 7 days, at least one of them is a Rest day.
%
% Example violation:
%       roster = [1,2,4,2,2,2,2,  
%                 3,3,4,3,3,1,1] 
% This solution has 11 working days in a row, starting on Tuesday in week 1 
% and ending on Saturday in week 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint
   forall (d in 1..flatsize) 
          (at_least(1,[longflatroster[d2]|d2 in d..d+6],Rest)) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Too Much Rest Constraint
%
% Description:
% Ensure that there is no sequence of three Rest days in a row
%
% Example violation:
%       roster = [1,2,4,2,2,2,2,  
%                 3,3,4,3,3,1,1]
% This solution has three Rest days in a row, starting on the Saturday of
% week 2 and ending on the Monday of week 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint
    forall (d in 1..flatsize) 
           (at_most(3,[longflatroster[d2]|d2 in d..d+3],Rest)) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Soft Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Not Evening before Morning Constraint
%
% Description:
% For every occurrence in the roster of an Eve shift (4) followed by a Morn
% shift (2) incur a cost of 1.  Sum up these costs over the whole roster
%
% Example Violation:
%       roster = [1,2,4,2,2,2,2,  
%                 3,3,4,3,3,1,1] 
%
% On Tuesday of week 1 there is an Eve shift followed by a Morn shift on
% Wednesday.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The proposition condition
% flatroster[d]=Eve /\ flatroster[(d mod flatsize)+1] = Morn
% is true whenever an Eve is followed by a Morn.
% bool2int converts true to a cost of 1.  If the proposition is false
% (i.e. the constraint is not violated), then bool2int returns 0.
% The sum over all sequences is therefore the number of violations
constraint
    evemorn = sum(d in 1..flatsize)
          (bool2int(flatroster[d]=Eve /\ 
                    longflatroster[d+1] = Morn )
          );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% No Isolated Rest Day Constraint
%
% Description:
% An isolated Rest day is a Rest day with a non-Rest-day on the day before and
% on the day after.  Each such isolated Rest day incurs a cost of 1, and the
% costs are summed up over the whole roster.
%
% Example Violation:
%       roster = [1,2,4,2,2,2,2,  
%                 1,3,4,3,3,1,1]
% The Monday of week 2 is preceded by a Morn shift and followed by a Day shift.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Using the syntax != for 'not-equals', the propositional formula
% flatroster[d-1] != Rest /\ flatroster[d] = Rest /\ flatroster[d+1] != Rest
% holds if and only if d is an isolated Rest day.

constraint
    isolated = sum(d in 1..flatsize)
                  (bool2int(    (longflatroster[d+1] = Rest /\
                   not(flatroster[d] = Rest \/ longflatroster[d+2] = Rest)))
                  ) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Solve Item
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A solution with minimal cost (evemorn+isolated) due to violations is sought.
% There may be different solutions with the same, minimal, cost.
% Only one solution is found by this model

% Unfortunately the facilities for controlling search, which are necessary for 
% getting good solving performance on most problems, have not been covered in FIT3022
% This model works well on all the data instances provided, but unfortunately
% small changes to the model can unpredictably, and dramatically, impact performance.

solve
    :: int_search(flatroster, first_fail, indomain_min, complete)
    minimize objective;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Output of the solution
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The roster is displayed as numbers - not unfortunately shift type names - with
% one row for each week.
% The number of isolated rests and morning after evening violations is also shown.

output ["Roster: \n"] 
       ++ [show([roster[i,j]|j in 1..7])++"\n"|i in 1..weeks] 
       ++ ["Isolated Rests: " ++ show(isolated) ++ "\n"] 
       ++ ["Morning after evening: " ++ show(evemorn) ++ "\n"];
  
