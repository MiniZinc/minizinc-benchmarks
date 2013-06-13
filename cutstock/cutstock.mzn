% vim: ft=zinc ts=4 sw=4 et tw=0

int: L;     % Stock length
int: K;     % Upper bound on number of stock pieces
set of int: Pieces;
Pieces = 1..K;

int: N;     % Number of items
set of int: Items;
Items = 1..N;

array[Items] of int: i_length;
array[Items] of int: i_demand;

% Determine K 
% I currently add 1 to the outer division, since mzn rounds down.
K = sum(i in Items)(  ( i_demand[i] div (L div i_length[i]) ) + 1 );

array[Pieces]        of var 0..1: pieces; 
array[Pieces, Items] of var 0..max(i_demand): items;

constraint
    forall(i in Items) ( 
        sum(k in Pieces)(items[k, i]) >= i_demand[i] 
    );

constraint
        forall(k in Pieces)(
            sum(i in Items) ( items[k, i] * i_length[i] ) <= pieces[k] * L
        );

solve 
    minimize sum(k in Pieces)(pieces[k]);

output [
    "pieces = ", show(pieces), "\n",
    "items = ", show(items), "\n"
];

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
