%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Mining itemsets with maximal accuracy

% A traditional task in machine learning is the task of concept learning.
% Given a dataset of positive and negative examples, the aim is here to find a 
% formula in disjunctive normal form which characterizes the positive examples 
% as accurately as possible. In this challenge this task is modeled as a 
% discrete constraint optimization problem; the aim is to find a formula which 
% is as accurate as possible.
% 
% The model is based on the link between DNF formulas and pattern sets in the 
% data mining literature. It represents the formula as a set of itemsets, and 
% imposes constraints on both the itemsets and the set of itemsets. It is based 
% on the 'Constraint Programming for Itemset Mining' framework (CP4IM); see 
% 
% http://dtai.cs.kuleuven.be/CP4IM/
%
% See AIJ article 'Itemset mining: A constraint programming perspective'
% http://dx.doi.org/10.1016/j.artint.2011.05.002

include "globals.mzn";

% The size of the set to be found
int: K;

% Given
int: NrI;
int: NrT_pos; int: NrT_neg;

array [1..NrT_pos] of set of int: TDB_pos;
array [1..NrT_neg] of set of int: TDB_neg;

% Variables

array [1..K,1..NrI] of var bool: Items;
array [1..K,1..NrT_pos] of var bool: TransP;
array [1..K,1..NrT_neg] of var bool: TransN;

% joint transactions
array [1..NrT_pos] of var bool: Trans_pos;
array [1..NrT_neg] of var bool: Trans_neg;

var -NrT_neg..NrT_pos : objective = 
  sum(t in 1..NrT_pos) (bool2int(Trans_pos[t])) -
  sum(t in 1..NrT_neg) (bool2int(Trans_neg[t]));
% Pattern 1
constraint % encode TDB: every Trans its complement has no supported Items
    forall(d in 1..K, t in 1..NrT_pos) (
        TransP[d,t] <-> sum(i in 1..NrI) (bool2int(not (i in TDB_pos[t])) * bool2int(Items[d,i])) <= 0
    );
constraint % encode TDB: every Trans its complement has no supported Items
    forall(d in 1..K, t in 1..NrT_neg) (
        TransN[d,t] <-> sum(i in 1..NrI) (bool2int(not (i in TDB_neg[t])) * bool2int(Items[d,i])) <= 0
    );
constraint % closed on positives: an Item is in, iff all Trans_pos where the Item is not in are 0
    forall(d in 1..K, i in 1..NrI) (
        Items[d,i] <-> sum(t in 1..NrT_pos) (bool2int(not (i in TDB_pos[t])) * bool2int(TransP[d,t])) <= 0
    );

% Canonical form (breaking symmetry)
constraint % lexicographic ordering of the trans
    forall(d in 1..K-1) (
        lex_less([TransP[d,t]|t in 1..NrT_pos],
                 [TransP[d+1,t]|t in 1..NrT_pos])
    /\  lex_less([TransN[d,t]|t in 1..NrT_neg],
                 [TransN[d+1,t]|t in 1..NrT_neg])
    );

% Joint coverage
constraint % covered when OR of any pattern
    forall(t in 1..NrT_pos) (
        Trans_pos[t] <-> exists (d in 1..K) (TransP[d,t])
    );
constraint % covered when OR of any pattern
    forall(t in 1..NrT_neg) (
        Trans_neg[t] <-> exists (d in 1..K) (TransN[d,t])
    );
    
solve
    :: bool_search(array1d(1..K*NrI,Items), input_order, indomain_max, complete)
	maximize objective;

output [
	"objective = ", show(objective), ";\n",
	"Items = ", show(Items), ";\n"
];
