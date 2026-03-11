%
% This is a model for a direct construction of a mono-matching game.
%
% This type of game is most well-known as Dobble or Spot-It (https://en.wikipedia.org/wiki/Dobble), 
% and contains a set of cards with symbols on them. Each pair of cards share a single symbol.
%
% There are mathematical constructions for creating monomatching games using finite projective planes 
% or cyclic difference sets. This model is not intended for efficiently construcing these sets using 
% such methods, it is intended as a stress test for set variables with simple set constraints.
%
% By Mikael Zayenz Lagerkvist, 2021
%
% Licensed under the MIT license (https://opensource.org/licenses/MIT)
%
% Search annotation modified by MiniZinc Challenge Organisers
%

include "globals.mzn";

% The order of the set.
%
% The order describes the number of finite projective plane construction.
%
int: n;

% Percentage of possible cards to create
float: card_percentage;


% The number of possible cards and symbols for the given order.
int: items = n * n + n + 1;

set of int: Cards = 1..floor(items*card_percentage);
set of int: Symbols = 1..items;

array[Cards] of var set of Symbols: cards;
%array[Symbols] of var Cards: pairs;

%constraint forall(symbol in Symbols) (
%    pairs[symbol] = sum(i, j in Cards where i < j) (
%      {symbol} == (cards[i] intersect cards[j])
%    )
%);

constraint forall(c in cards) ( 
    card(c) == n
);

constraint forall(i, j in Cards where i < j) (
    card(cards[i] intersect cards[j]) == 1
);

constraint all_different(cards);

%solve :: set_search(cards, dom_w_deg, indomain) satisfy;
%solve satisfy;

% Workaround for incorrect definition of set_search in nosets.mzn
bool: nosets_set_search = show(set_search([{}], input_order, indomain_min, complete)) = "seq_search([bool_search(set2bools(xx[i]),a1,a2,a3) | i in index_set(xx), ])";
solve :: set_search(cards, input_order, if nosets_set_search then indomain_max else indomain_min endif) satisfy;
