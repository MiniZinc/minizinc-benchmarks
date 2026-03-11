%------------------------------------------------------------------------------
% Parameters

int: f;
int: g;
int: c;
int: k;
set of int: Cap = 0..k;
int: t;
set of int: Trips = 1..t;
set of int: Trips0 = 0..t;
int: pf;
int: pg;
int: pc;
int: maxp = f*pf + g*pg + c*pc;

%------------------------------------------------------------------------------
% Variables

array[Trips] of var Cap: fox;
array[Trips] of var Cap: geese;
array[Trips] of var Cap: corn;
var 0..t: trips;

array[Trips0] of var 0..f: efox;
array[Trips0] of var 0..g: egeese;
array[Trips0] of var 0..c: ecorn;

array[Trips0] of var 0..f: wfox;
array[Trips0] of var 0..g: wgeese;
array[Trips0] of var 0..c: wcorn;

var 0..maxp: objective;

%------------------------------------------------------------------------------
% Predicates

predicate alone(
    var 0..f:   fox0, var 0..f:   fox1,
	var 0..g: geese0, var 0..g: geese1,
	var 0..c:  corn0, var 0..c:  corn1
) =
    let { var 1..4: c; % the cases we consider 
                       % 1: only one type of goods
                       % 2: no fox, geese and corn
                       % 3: fox and corn, no geese
                       % 4: fox and geese (corn or not)
    } in (
        c = [1,1,1,2,1,3,4,4][1 + 4*(fox0 > 0) + 2*(geese0 > 0) + (corn0 > 0)] 
    /\   fox1 = fox0 + [0,0,-1,if fox0 > geese0 then -1 else 0 endif][c] 
    /\   geese1 = geese0 + [0,if geese0 > corn0 then -1 else 0 endif, 0, if fox0 > geese0 then 0 else -fox0 endif][c] 
    /\   corn1 = corn0 + [0,if geese0 > corn0 then -1 else -geese0 endif, -1, 0][c]
    );

%------------------------------------------------------------------------------
% Constraints

constraint efox[0] = 0 /\ egeese[0] = 0 /\ ecorn[0] = 0;
constraint wfox[0] = f /\ wgeese[0] = g /\ wcorn[0] = c;

constraint forall(i in 1..t)(
    i <= trips -> 
	    if i mod 2 == 1 then
	        alone(
                  wfox[i-1] -   fox[i],   wfox[i],
	     	    wgeese[i-1] - geese[i], wgeese[i],
		         wcorn[i-1] -  corn[i],  wcorn[i]
            ) 
        /\  efox[i] = efox[i-1] + fox[i] 
        /\  egeese[i] = egeese[i-1] + geese[i]
		/\  ecorn[i] = ecorn[i-1] + corn[i]
	    else
		    alone(
                  efox[i-1] -   fox[i],   efox[i],
	     	    egeese[i-1] - geese[i], egeese[i],
		         ecorn[i-1] -  corn[i],  ecorn[i]
            )
        /\  wfox[i] = wfox[i-1] + fox[i]
		/\  wgeese[i] = wgeese[i-1] + geese[i]
		/\  wcorn[i] = wcorn[i-1] + corn[i]
	    endif
);

constraint forall(i in 1..t)(fox[i] + geese[i] + corn[i] <= k);

constraint forall(i in 1..t)(i > trips -> fox[i] = 0 /\ geese[i] = 0 /\ corn[i] = 0);

constraint objective = efox[trips] * pf + egeese[trips] * pg + ecorn[trips] * pc;

%------------------------------------------------------------------------------
% Solve item

solve 
    :: seq_search([
        int_search([trips], input_order, indomain_min, complete),
        int_search(
            [ if j= 1 then fox[i] elseif j = 2 then geese[i] else corn[i] endif 
            | i in Trips, j in 1..3], 
            input_order,indomain_max, complete
        )
    ])          
    maximize objective;


%------------------------------------------------------------------------------
% Redundant constraints

constraint redundant_constraint(
    forall(i in 1..t)( 
          wfox[i-1] +   efox[i-1] >=   wfox[i] +   efox[i]
    /\  wgeese[i-1] + egeese[i-1] >= wgeese[i] + egeese[i]
    /\   wcorn[i-1] +  ecorn[i-1] >=  wcorn[i] +  ecorn[i]
    )
);
   

%------------------------------------------------------------------------------
% Output item

output [
    "fox = \(fox);\n",
    "geese = \(geese);\n",
    "corn = \(corn);\n",
    "trips = \(trips);\n",
    "objective = \(objective);\n"
];

