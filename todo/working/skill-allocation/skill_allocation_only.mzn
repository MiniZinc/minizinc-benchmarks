include "globals.mzn";

%%% Date file
% include "skill_allocation_mzn_4d_1.dzn";
% include "skill_allocation_mzn_4d_2.dzn";
% include "skill_allocation_mzn_5d_1.dzn";
% include "skill_allocation_mzn_5d_2.dzn";
% include "skill_allocation_mzn_5d_3.dzn";
% include "skill_allocation_mzn_2w_1.dzn";
% include "skill_allocation_mzn_2w_2.dzn";
% include "skill_allocation_mzn_1m_1.dzn";
% include "skill_allocation_mzn_1m_2.dzn";
% include "skill_allocation_mzn_1m_3.dzn";
% include "skill_allocation_mzn_2m_1.dzn";
% include "skill_allocation_mzn_2m_2.dzn";
% include "skill_allocation_mzn_2m_3.dzn";
% include "skill_allocation_mzn_3m_1.dzn";
% include "skill_allocation_mzn_3m_2.dzn";
% include "skill_allocation_mzn_3m_3.dzn";

%%%%%% Input %%%%%%%
int: nNewSkillsPerPerson;   % Number of new skills a person is allowed to learn
int: nTrainingCap = -1;      % Number of training allowed in during the considered period in total. This is to put a cap on the training budget.
int: nInterstateCap = -1; % -1 - no cap
int: nOverseasCap = 5; % -1 - no cap
int: nMaxJobs;   % Maximum number of jobs a person is allowed to perform, 0 - switch off the constraint
int: nMinJobs = 0;   % Minimum number of jobs a person is allowed to perform, 0 - switch off the constraint
bool: allEng = false;  % Allow an engineer to perform any job, i.e. skill matching contraint is not applied.
%%%%%%%%%%%%%%%%%

%%% All Skills
array[int] of string: sSkills;
set of int: SKILLS = index_set(sSkills);

%%% Training
set of int: TRAINING = 1..nNewSkillsPerPerson;

%%% Employee data
array[int,int] of int: engineer_skills;
array[int] of int: engineer_location; % Postcode
set of int: ENGS = index_set_1of2(engineer_skills);

%%% Service Calls
array[int,int] of int: jobs;
set of int: JOBS = index_set_1of2(jobs);


%%% DECISION VARIABLES
array[JOBS] of var ENGS: allocations;


%%% Set of possible engineers for each job
array[ENGS,TRAINING] of var 0..0 union SKILLS: new_skills;
constraint forall(e in ENGS, t in TRAINING)(
let {
  set of int: NEWSKILLS = {s | s in SKILLS where engineer_skills[e,s]==0}
} in
   new_skills[e,t] in 0..0 union NEWSKILLS 
);
constraint if allEng then true else forall(i in JOBS)(
let {
  set of int: POSENGS = {e | e in ENGS where engineer_skills[e,jobs[i,1]] == 1}, 
} in
  (allocations[i] in POSENGS)
  \/ exists(e in ENGS, t in TRAINING)(jobs[i,1] == new_skills[e,t] /\ allocations[i]==e)
) endif;
constraint if nTrainingCap < 0 then true else sum(e in ENGS, t in TRAINING)(
   new_skills[e,t] > 0 
)<=nTrainingCap 
endif;


%%% Number of jobs allowed per engineer
constraint 
  if nMaxJobs == 0 then true else forall(e in ENGS)(
    sum(i in JOBS)( allocations[i] == e) <= nMaxJobs )
  endif
;
constraint 
  if nMinJobs <= 0 then true else forall(e in ENGS)(
    sum(i in JOBS)( allocations[i] == e) >= nMinJobs )
  endif
;
%%% Number of jobs overseas jobs per engineer
constraint 
  if nOverseasCap < 0 then true else forall(e in ENGS)(
    sum(i in JOBS)( (allocations[i] == e) * (jobs[i,5]==1) ) <= nOverseasCap )
  endif
;

%%% Number of jobs interstate jobs per engineer
constraint
  if nInterstateCap < 0 then true else forall(e in ENGS where engineer_location[e] > 0)(
    sum(i in JOBS)( (allocations[i] == e) * not (ceil(jobs[i,4]/1000) == ceil(engineer_location[e]/1000) ) ) <= nInterstateCap )
  endif;

var int: objective;
constraint objective == sum(e in ENGS, t in TRAINING)(
   new_skills[e,t] > 0 
);

solve
::seq_search( [
    int_search([new_skills[e,t] | t in TRAINING, e in ENGS],input_order, indomain_min, complete),
    int_search([allocations[i] | i in JOBS],input_order, indomain_min, complete),
])
minimize objective;

output [
	"allocations = array1d(\(JOBS), \(allocations));\n",
	"new_skills = array2d(\(ENGS), \(TRAINING), \(new_skills));\n",
	"objective = \(objective);\n"
];


% output 
% ["Eng \(e): " ++ show( sort([i| i in JOBS where fix(allocations[i])==e])) ++ "\n"  | e in ENGS where length([i | i in JOBS where fix(allocations[i])==e])>0 ] ++
% ["Allocations: \(allocations)\n" ] ++
% ["New Skill of Eng \(e): " ++ show( sort([new_skills[e,t]| t in TRAINING where fix(new_skills[e,t])>0])) ++ "\n"  | e in ENGS where length([new_skills[e,t]| t in TRAINING where fix(new_skills[e,t])>0])>0 ] ++
% ["Total Jobs - \(card(JOBS))\n"] ++
% ["Obj - NoOfTraining: \(objective)"];
