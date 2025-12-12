enum VACCINE;

enum AGE = { BABY, CHILD, YOUTH, ADULT, SENIOR, AGED, ANCIENT };
enum GENDER = { FEMALE, MALE, OTHER };
enum HEALTH = { GOOD, POOR, COMPROMISED };
enum EXPOSURE = { LOW, AVERAGE, HIGH, EXTREME };

int: m; % number of groups
set of int: GROUP = 1..m;
array[GROUP] of AGE: age;           % age of the group
array[GROUP] of GENDER: gender;     % gender of the group
array[GROUP] of HEALTH: health;     % underlying health of the group
array[GROUP] of EXPOSURE: exposure; % exposure for the group
array[GROUP] of int: size;          % number of people in the group

int: minsize;                       % min number of people is a group/vaccine trial
array[AGE] of int: age_group_min;   % min number of groups for each age
array[AGE] of int: age_group_max;   % max number of groups for each age
int: max_people_diff;               % max diff in total people trial on diff vaccines
int: max_share_vaccines;            % max number of shared vaccines by groups

array[HEALTH] of int: health_information;      % value of information by health
array[EXPOSURE] of int: exposure_information;  % value of information by exposre

array[GROUP] of var set of VACCINE: x;


%=============================================================================

% maximum number of vaccines for each group
constraint forall(g in GROUP)(card(x[g]) <= size[g] div minsize);

% maximum and minimum number of groups for each vaccine and age
include "global_cardinality_low_up.mzn";
constraint forall(v in VACCINE)
     (global_cardinality_low_up( [ (v in x[g])*age[g] | g in GROUP ],
                                 AGE, age_group_min, age_group_max));
array[VACCINE, AGE] of var int: vaccine_age  = array2d(VACCINE, AGE, [ sum(g in GROUP where age[g] = a)(v in x[g]) | v in VACCINE, a in AGE]);                                 
 
% difference in tested people
int: total_participants = sum(size);
array[VACCINE] of var 0..total_participants: total = 
     [ sum(g in GROUP)
          (if v in x[g] then size[g] div card(x[g]) else 0 endif)
     | v in VACCINE ];
constraint forall(v1,v2 in VACCINE where v1 < v2)
	   	 (abs(total[v1] - total[v2]) <= max_people_diff);

% no gender balace
array[GENDER,VACCINE] of var 0..m: ngroups =
     array2d(GENDER,VACCINE,
            [ sum(g in GROUP where gender[g] = gen)(v in x[g])
            | gen in GENDER, v in VACCINE ]);
constraint forall(gen in GENDER)
                 (forall(v1,v2 in VACCINE where v1 < v2)
                  (ngroups[gen,v1] = ngroups[gen,v2]));

% shares vaccines
constraint forall(g1,g2 in GROUP where g1 < g2)
                 (card(x[g1] intersect x[g2]) <= max_share_vaccines);

bool: extension = true; 

array[VACCINE] of var int: information =
     array1d(VACCINE,
             [ sum(g in GROUP)((v in x[g])*
                if extension /\ exists(g1 in GROUP where g1 < g /\ health[g] = health[g1] /\ exposure[g] = exposure[g1])(v in x[g1]) 
                   then 1 else 
                        health_information[health[g]] * exposure_information[exposure[g]] 
                   endif
                )
             | v in VACCINE ]);

var int: objective = min(information);
solve :: int_search(array1d(vg), input_order, indomain_max)
      maximize objective;


output ["x = \(x);\n"];
output [ show2d(vaccine_age),"\n" ];
output [ show2d(ngroups),"\n" ];
output ["total = \(total);\n"];
output ["information = \(information);\nobj = \(min(information));\n"];

int: vl = max([ string_length(show(v)) | v in VACCINE ]);
output [ format_justify_string(-vl- 2, "group: ") ] ++ [ format_justify_string(11,show(g)) ++ " " | g in GROUP ] ++ ["\n"];
output [ format_justify_string(-vl- 2, "age: ") ] ++ [ format_justify_string(11,show(age[g])) ++ " " | g in GROUP ] ++ ["\n"];
output [ format_justify_string(-vl- 2, "gender: ") ] ++ [ format_justify_string(11,show(gender[g])) ++ " " | g in GROUP ] ++ ["\n"];
output [ format_justify_string(-vl- 2, "health: ") ] ++ [ format_justify_string(11,show(health[g])) ++ " " | g in GROUP ] ++ ["\n"];
output [ format_justify_string(-vl- 2, "expose: ") ] ++ [ format_justify_string(11,show(exposure[g])) ++ " " | g in GROUP ] ++ ["\n"];
output [ if g = min(GROUP) then format_justify_string(-vl,show(v)) ++ ": " else "" endif ++
         show_int(11, v in x[g]) ++ " " ++ 
         if g = max(GROUP) then "\n" else "" endif 
       | v in VACCINE, g in GROUP ];
 
%=============================================================================
% Symmetry Breaking
%=============================================================================
include "lex_lesseq.mzn";
array[VACCINE, GROUP] of var 0..1: vg = array2d(VACCINE, GROUP, [ v in x[g] | v in VACCINE, g in GROUP ]);
constraint symmetry_breaking_constraint(forall(v in VACCINE where v != max(VACCINE)) 
                 (lex_lesseq( vg[v,..], vg[enum_next(VACCINE,v),..] )));
