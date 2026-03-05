%%%%%%%%%%%%%%%%%%%%%%%%%
% Cable Tree Wiring
%%%%%%%%%%%%%%%%%%%%%%%%%

include "globals.mzn";
int: k;
set of int: Positions = 1..k;
set of int: Cavities = Positions;
int: b;
set of int: ChamberPairs = 1..2*b;
set of int: CableStarts = 1..b;

array[int,int] of Cavities: AtomicConstraints;
array[int,int] of Cavities: DisjunctiveConstraints;
array[int] of Cavities: DirectSuccessors;
array[int,int] of Cavities: SoftAtomicConstraints;

array[Cavities] of var Positions: pfc;
constraint all_different(pfc);


constraint forall (i in index_set_1of2(AtomicConstraints)) ( pfc[AtomicConstraints[i,1]] < pfc[AtomicConstraints[i,2]] );
constraint forall (i in index_set_1of2(DisjunctiveConstraints)) (
  ( pfc[DisjunctiveConstraints[i,1]] < pfc[DisjunctiveConstraints[i,2]] \/
    pfc[DisjunctiveConstraints[i,3]] < pfc[DisjunctiveConstraints[i,4]] ) /\
  if DisjunctiveConstraints[i,1]==DisjunctiveConstraints[i,3] then
    max(pfc[DisjunctiveConstraints[i,2]], pfc[DisjunctiveConstraints[i,4]]) > pfc[DisjunctiveConstraints[i,1]]
  else true endif
);

constraint forall (i in index_set(DirectSuccessors)) (
  if DirectSuccessors[i]<= b then
    pfc[DirectSuccessors[i]] < pfc[DirectSuccessors[i]+b] -> pfc[DirectSuccessors[i]] +1 = pfc[DirectSuccessors[i]+b]
  else
    pfc[DirectSuccessors[i]] < pfc[DirectSuccessors[i]-b] -> pfc[DirectSuccessors[i]] +1 = pfc[DirectSuccessors[i]-b]
  endif
);

var int: S = if b=0 then 0 else sum(i in CableStarts) (abs(pfc[i]-pfc[i+b]) > 1) endif;
var int: M = if b=0 then 0 else
	(max(i in ChamberPairs) 
		(sum(j in ChamberPairs where j<=b) (pfc[j] < pfc[i] /\ pfc[i] < pfc[j+b])
		 + sum(j in ChamberPairs where j>b) (pfc[j] < pfc[i] /\ pfc[i] < pfc[j-b])))
		 endif;

var int: L = if b=0 then 0 else max(i in CableStarts) (abs(pfc[i]-pfc[i+b])-1) endif;

var int: N = sum(i in index_set_1of2(SoftAtomicConstraints)) (pfc[SoftAtomicConstraints[i,1]] > pfc[SoftAtomicConstraints[i,2]]);

var int: objective = S*pow(k,3)+M*pow(k,2)+L*pow(k,1)+N;

% Redundant dual model via inverse constraint

array[Positions] of var Cavities: cfp;
constraint redundant_constraint(all_different(cfp));

solve ::int_search(pfc, first_fail, indomain_split) minimize objective;

% output ["\([S,M,L,N])\n\(objective)\n\(pfc)\n"];

output [
  "objective = \(objective);\n",
  "pfc = array1d(\(Cavities), \(pfc));\n",
];
