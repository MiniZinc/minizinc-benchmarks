%% Model for the Capacitated Concert Hall problem.
%% Each hall has a maximum capacity, and each concert
%% has a size requirement.
%% Author: Graeme Gange, 04/2018
include "globals.mzn";

int: num_offers;
int: num_halls;

set of int: Offer = 1..num_offers;
set of int: Hall = 1..num_halls;
set of int: Hall0 = 0..num_halls;

array [Offer] of int: start;
array [Offer] of int: end;
array [Offer] of int: price;

set of int: Time = min(start)..max(end);

array [Offer] of var Hall0: assign;

function bool: overlaps(Offer: o, Time: t) = start[o] <= t /\ t < end[o];
array [Offer] of set of Offer: cliques = [ { p | p in Offer where overlaps(p, start[o]) } | o in Offer ];
function bool: clique_is_maximal(set of Offer: c) = forall (d in cliques where card(d) > card(c)) (not (c subset d));

%% Overlapping events cannot share a hall.
constraint forall (clique in cliques where clique_is_maximal(clique)) (alldifferent_except_0([assign[o] | o in clique]) :: bounds);

array [Hall] of int: capacity;
array [Offer] of int: requirement;

array [int] of Offer: ordered_offer = arg_sort(requirement);
function set of Hall: feasible_halls(Offer: o) = { h | h in Hall where capacity[h] >= requirement[o] };
function set of Offer: feasible_offers(Hall: h) = { o | o in Offer where capacity[h] >= requirement[o] };

%% Needed for symmetry breaking predicates
function set of Hall: eqclass(Hall: h) = { g | g in Hall where feasible_offers(h) = feasible_offers(g) };

function bool: dominates(Offer: p, Offer: q) =
  start[q] <= start[p] /\ end[p] <= end[q]
  /\ feasible_halls(q) subset feasible_halls(p)
  /\ price[p] >= price[q]
  /\ (price[p] > price[q] \/ p < q);

constraint forall (o in Offer) (assign[o] in {0} union feasible_halls(o));

%% Symmetry and dominance breaking constraints
bool: break_dominance = false;
bool: break_symmetry = true;

constraint
  if break_dominance then
    forall (p, q in Offer where dominates(p, q)) (symmetry_breaking_constraint(assign[q] > 0 -> assign[p] > 0))
  else true endif;
constraint
  if break_symmetry then
    forall (h in Hall) (symmetry_breaking_constraint(value_precede_chain(eqclass(h), assign)))
  else true endif;

int: lb_obj = min(0, sum(o in Offer where price[o] < 0)(price[o]));
int: ub_obj = max(0, sum(o in Offer where price[o] > 0)(price[o]));
var lb_obj..ub_obj: objective;
constraint objective = sum (o in Offer) (price[o] * (assign[o] > 0));

solve
  :: int_search(
      [assign[p] <= 0 | p in arg_sort([-price[h]/(end[h] - start[h] + 1)
                                    | h in Hall])] ++ assign,
      input_order, indomain_min, complete)
    maximize objective;

output [
	"assign = \(assign);\n",
	"objective = \(objective);\n"
];
