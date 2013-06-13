% NOTE: this version of the rostering model was used in the 2009
% MiniZinc challenge.  It no longer works because this formulation
% relies on the MiniZinc 1.0 semantics for the mod operation.
% These were change in MiniZinc 1.1; as a result this model is now
% unsatisfiable.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  FIT3022 
%  Assignment 1
%  Rostering Problem
%  Efficient Solution
%  5th May 2009
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

% weeks and reqt are imported from the data file.
% flatsize is a constant computed from the parameter weeks, which is used 
% in the model
int: weeks ;
int: flatsize = 7 * weeks ;
array [1..5,1..7] of int: reqt ;
int: minobj ;

% The following parameters aid readability of the model
int:Rest=1;
int:Morn=2;
int:Day=3;
int:Eve=4;
int:Joker=5;

% The following two variables will hold the costs due to violated soft constraints
var 0..flatsize: evemorn ;
var 0..flatsize: isolated ;

var 0..2*flatsize: objective :: is_output = evemorn+isolated ;

% The roster is an array of decision variables:
% each variable has domain 1..5 representing possible shifts Rest,Morn,Day,Eve or Joker
% roster is a two-dimensional array with a row for each week
array [1..weeks,1..7] of var 1..5: roster :: is_output ;
% flatroster is a one-dimensional array, which will contain exactly the same set of variables
array [1..flatsize] of var 1..5: flatroster ;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint objective >= minobj ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Hard Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Roster Flat-Roster constraint
%
% Description:
% This constraint ensures that roster and flatroster contain the same set of variables
% The first seven variables in flatroster correspond to the first row (week) in roster.
% The 8th to the 14th variables in flatroster correspond to the second row in roster, etc.
% The total number of variables is the number of weeks times 7
%
% Example violation:
% This constraint is violated if a variable in flatroster is different from the corresponding
% variable in roster, e.g.
% flatroster = [1,2,2,2,2,2,2,2,2,2,2,2,2,2]
% roster     = [2,2,2,2,2,2,2,
%               2,2,2,2,2,2,2]
% The first day of week one is different in flatroster and roster
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint 
    forall (shift in 1..5)
            (forall (day in 1..7) 
                    (exactly(reqt[shift,day],[roster[week,day] | week in 1..weeks],shift))
            ) ;

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

% Note the use of ((d2-1) mod flatsize)+1
% which has the same value as d2 except when d2 is greater than flatsize.
% When d2 = flatsize+1 (equivalent to Monday of week 1), it takes the value 1
% When d2 = flatize+n (for any n less than flatsize), it takes the value n
% ... but see note ALTERNATIVE below

constraint
   forall (d in 1..flatsize) 
          (at_least(1,[flatroster[((d2-1) mod flatsize)+1]|d2 in d..d+6],Rest)) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ALTERNATIVE
% Some answers have used a more elegant solution: appending the first 6 days of the roster
% onto the end to make an extended roster.  The total length of the extended roster is 7*weeks+6.
% This avoids any need for the formula ((d2-1) mod flatsize)+1. The simple variable d2 can be used.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Too Much Rest Constraint
%
% Description:
% Ensure that there is no sequence of more than three Rest days in a row
%
% Example violation:
%       roster = [1,1,4,2,2,2,2,  
%                 3,3,4,3,3,1,1]
% This solution has four Rest days in a row, starting on the Saturday of
% week 2 and ending on the Monday of week 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% We associate a count with each day recording the number of 
% consecutive rest days.  On each rest day we increment the count by 1.
% The count is not allowed to be larger than 3.
% Note again the use of ((d-2) mod flatsize)+1
array [1..flatsize] of var 0..3: restseq;
constraint
    forall (d in 1..flatsize)
           ( (flatroster[d] = Rest -> restseq[d] = 1+restseq[((d-2) mod flatsize)+1] )
              /\ ( restseq[d] = 0 <-> flatroster[d] != Rest )
           ) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Soft Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Not Evening before Morning Constraint
%
% Description:
% For every occurrence in the roster of an Eve shift (4) followed by a Morn shift (2)
% incur a cost of 1.  Sum up these costs over the whole roster
%
% Example Violation:
%       roster = [1,2,4,2,2,2,2,  
%                 3,3,4,3,3,1,1] 
% On Tuesday of week 1 there is an Eve shift followed by a Morn shift on Wednesday.
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
                    flatroster[(d mod flatsize)+1] = Morn )
          ) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% No Isolated Rest Day Constraint
%
% Description:
% An isolated Rest day is a Rest day with a non-Rest-day on the day before and on the day after.
% Each such isolated Rest day incurs a cost of 1, and the costs are summed up over the whole roster.
%
% Example Violation:
%       roster = [1,2,4,2,2,2,2,  
%                 1,3,4,3,3,1,1]
% The Monday of week 2 is preceded by a Morn shift and followed by a Day shift.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The propositional formula
% flatroster[d] = Rest -> flatroster[d-1] = Rest \/ flatroster[d+1] = Rest
% holds UNLESS d is an isolated Rest day.
% To handle cyclic rosters this constraint uses ((Expr-1) mod flatsize)+1 instead of Expr throughout
constraint
    isolated = sum(d in 1..flatsize)
                  ( bool2int(  flatroster[d] = Rest /\
                               not (flatroster[((d-2) mod flatsize)+1] = Rest \/
                                    flatroster[(d mod flatsize)+1] = Rest )      
                            )
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

%%%%%%%%%%%%%%%%%   Search Optimisation %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
int: restshiftct = sum(day in 1..7)(reqt[Rest,day]) ;

%  These are the (unknown) days which will be assigned as rest days
array [ 1.. restshiftct ] of var 1..flatsize: restdays ;

% The flat array linearises the roster column by column 
% (viz. d1w1, d1w2, ...,d2w1,d2w2,...) 
% to ensure that when searching on restdays, the rests are assigned day by day

array [1..flatsize] of var 1..5: flat2 ;
constraint 
    forall (d in 1..7,w in 1..weeks) (flat2[weeks*(d-1)+w] = roster[w,d]) ; 

% We list the roster days when the rest days will occur in increasing order.
constraint
    forall (x in 1..restshiftct-1) (restdays[x+1]>restdays[x]) ;

% A roster day can ONLY be a rest day if it occurs in restdays
constraint
    forall (x in 1..flatsize)
           ( (flat2[x] = Rest) <-> (exists (y in 1..restshiftct) (x = restdays[y])) ) ;


%%  Symmetry  
% Suppose the whole roster is complete
% We can simply choose week1 to be any week (since the roster is cyclic).
% Let's arbitrarily choose a week which starts with a rest day
% This avoids searching among similar rosters.
constraint
    roster[1,1] = Rest ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve
        % Try first to find rosters with a minimum number of isolated rest days
%     :: int_search([isolated],"input_order","indomain_min","complete")
     :: seq_search([
            int_search(restdays, input_order, indomain_min, complete),
            int_search(flat2, input_order, indomain_min, complete)
        ])
    minimize objective ;



