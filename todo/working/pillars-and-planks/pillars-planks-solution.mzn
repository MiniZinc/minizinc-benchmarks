% Use this editor as a MiniZinc scratch book
int: planks;
set of int: PLANK = 1..planks;
array[PLANK] of int: plank_width;
int: pillars;
set of int: PILLAR = 1..pillars;
array[PILLAR] of int: pillar_height;
array[PILLAR] of int: pillar_width;

int: available_width;
int: available_height;
set of int: WIDTH = 0..available_width-1;
set of int: HEIGHT = 0..available_height-1; 

array[PLANK] of var WIDTH: xk;
array[PLANK] of var HEIGHT: yk;

set of int: PLANK0 = 0..planks;
array[PLANK0] of int: plank_widthx = array1d(PLANK0, [available_width] ++ plank_width);
array[PLANK0] of var WIDTH: xkx = array1d(PLANK0, [0] ++ xk);
array[PLANK0] of var -1..available_height-1: ykx = array1d(PLANK0, [-1] ++ yk);


array[PILLAR] of var WIDTH: xr;
array[PILLAR] of var HEIGHT: yr;

constraint forall(p in PLANK)(xk[p] + plank_width[p]<= available_width);

constraint forall(p in PILLAR)(xr[p] + pillar_width[p]<= available_width);
constraint forall(p in PILLAR)(yr[p] + pillar_height[p]<= available_height);

% symmetry breaking
constraint symmetry_breaking_constraint(forall(p1,p2 in PLANK where p1 < p2 /\ plank_width[p1] = plank_width[p2])
                 (yk[p1] <= yk[p2] /\ (yk[p1] = yk[p2] -> xk[p1] < xk[p2])));

constraint symmetry_breaking_constraint(forall(p1,p2 in PILLAR where p1 < p2 /\ pillar_width[p1] = pillar_width[p2] /\ pillar_height[p1] = pillar_height[p2])
                 (yr[p1] <= yr[p2] /\ (yr[p1] = yr[p2] -> xr[p1] < xr[p2])));



include "diffn.mzn";
constraint diffn(xk ++ xr, yk ++ yr, plank_width++pillar_width, [1 | p in PLANK] ++ pillar_height);

% each plank is supported at both ends by a pillar
array[PLANK] of var PILLAR: left;
array[PLANK] of var PILLAR: right;
constraint forall(p in PLANK)( xr[left[p]] <= xk[p] /\ xr[left[p]] + pillar_width[left[p]] > xk[p] 
                               /\ yk[p] = yr[left[p]] + pillar_height[left[p]] );
constraint forall(p in PLANK)( xr[right[p]] <= xk[p] + plank_width[p] - 1 /\ xr[right[p]] + pillar_width[right[p]] > xk[p] + plank_width[p]-1 
                               /\ yk[p] = yr[right[p]] + pillar_height[right[p]] );

% each pillar sits on exaclty one plank
array[PILLAR] of var PLANK0: support;  
constraint forall(p in PILLAR)
                 (xr[p] >= xkx[support[p]] /\ xr[p] + pillar_width[p] <= xkx[support[p]] + plank_widthx[support[p]]
                  /\ yr[p] = ykx[support[p]] + 1);
                  
var 0..available_height: objective = max([ yk[p] + 1 | p in PLANK ] ++ [yr[p] + pillar_height[p] | p in PILLAR ]);                  
        

enum TYPE = {LK,RK,K,LP,RP,UP,IP,E};
array[WIDTH, HEIGHT] of TYPE: map :: output_only =
     array2d(WIDTH,HEIGHT, 
             [ if exists(p in PLANK)(fix(xk[p]) = x /\ fix(yk[p]) = y) then LK
               elseif exists(p in PLANK)(fix(xk[p]) + plank_width[p] = x+1 /\ fix(yk[p]) = y) then RK
               elseif exists(p in PLANK)(fix(xk[p]) < x /\ fix(xk[p]) + plank_width[p] > x+1 /\ fix(yk[p]) = y) then K
               elseif exists(p in PILLAR)(fix(xr[p]) = x /\ pillar_width[p] = 1 /\ fix(yr[p]) <= y /\ fix(yr[p]) + pillar_height[p] > y) then UP
               elseif exists(p in PILLAR)(fix(xr[p]) = x /\ fix(yr[p]) <= y /\ fix(yr[p]) + pillar_height[p] > y) then LP
               elseif exists(p in PILLAR)(fix(xr[p]) + pillar_width[p] = x +1 /\ fix(yr[p]) <= y /\ fix(yr[p]) + pillar_height[p] > y) then RP
               elseif exists(p in PILLAR)(fix(xr[p]) < x /\ fix(xr[p]) + pillar_width[p] > x+1 /\ fix(yr[p]) <= y /\ fix(yr[p]) + pillar_height[p] > y) then IP
               else E endif           
             | x in WIDTH, y in HEIGHT ]);                                  
                                      
array[TYPE] of string: rep = ["[","]","=","(",")","|","."," "];  
                      
output [ if x = 0 then "% " else "" endif ++
         let {int: y = fix(objective) - 1 - yy;} in 
         rep[map[x,y]]
         ++ if x = available_width-1 then "\n" else "" endif 
       | yy in 0..fix(objective)-1, x in WIDTH ];

   
output ["objective = \(objective);\n"];          
output ["xk = \(xk);\nyk = \(yk);\nxr = \(xr);\nyr = \(yr);\n"];             
                                          
solve :: seq_search([int_search(support,input_order,indomain_min),
                     int_search([ if j = 1 then left[pk] else right[pk] endif | pk in PLANK, j in 1..2], input_order, indomain_min),
                     int_search([ if j = 1 then xr[pr] else yr[pr] endif | pr in PILLAR, j in 1..2], input_order, indomain_min),
                     int_search([ if j = 1 then xk[pk] else yk[pk] endif | pk in PLANK, j in 1..2], input_order, indomain_min)])
      minimize objective;

                              
                                                                        
                  
                  