int: m; % number of people
set of int: PERSON = 1..m;
int: n; % number of goods
set of int: GOOD = 1..n;
array[GOOD] of int: available; % number of each good available
array[GOOD] of int: value;
array[PERSON] of int: npref;   % number of preferences for each person
int: tpref = sum(npref);
set of int: PREF = 1..tpref;
array[PREF] of GOOD: good_pref; % good for each preference
array[PREF] of int: req_pref;   % number required for each preference

int: maxreq = max(req_pref);
array[PERSON] of var GOOD: good;
array[PERSON] of var 0..maxreq: num;

array[PERSON] of int: cumpref = [ sum(p2 in PERSON where p2 < p)(npref[p2]) | p in PERSON ];
function GOOD: pref(PERSON: p, int: i) = good_pref[cumpref[p] + i];
function int: req(PERSON: p, int: i) = req_pref[cumpref[p] + i];


array[PERSON,GOOD] of 0..n: rank = array2d(PERSON,GOOD,
     [ max([ (pref(p,i) = g)*i | i in 1..npref[p] ]) | p in PERSON, g in GOOD ]);
array[PERSON,GOOD] of 0..maxreq: required = array2d(PERSON,GOOD,
     [ max([ (pref(p,i) = g)*req(p,i) | i in 1..npref[p] ]) | p in PERSON, g in GOOD ]);
     

% choose one preference for each person
array[PERSON] of var 1..max(npref): preference;
constraint forall(p in PERSON)(preference[p] <= npref[p]);
constraint forall(p in PERSON)(good[p] = good_pref[cumpref[p] + preference[p]]);     
constraint forall(p in PERSON)(num[p] = req_pref[cumpref[p] + preference[p]]);               
 
% ensure enough goods for each assignment, and calculate remainder                    
array[GOOD] of var 0..max(available): remainder;     
constraint forall(g in GOOD)
                 (sum(p in PERSON)((good[p] = g)*num[p]) + remainder[g]= available[g]);                      

% ensure the assignment is stable    
constraint forall(p1,p2 in PERSON where p1 < p2)
                 ( rank[p1,good[p1]] < rank[p1,good[p2]] \/ rank[p1,good[p2]] = 0 \/
                   rank[p2,good[p2]] < rank[p2,good[p1]] \/ rank[p2,good[p1]] = 0 \/
                   required[p1,good[p2]] - required[p2,good[p2]] > remainder[good[p2]] \/
                   required[p2,good[p1]] - required[p1,good[p1]] > remainder[good[p1]]);
var int: objective = sum(g in GOOD)(remainder[g]*value[g]);
solve :: int_search(preference, first_fail, indomain_min)
                      maximize objective;

var int: obj = sum(p in PERSON)(num[p]*value[good[p]]);

output ["objective = \(objective);\n"];
output ["obj = \(obj);\n"];
output ["good = \(good);\n"];
output ["num = \(num);\n"];
output ["preference = \(preference);\n"];
