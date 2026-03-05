% ===============================================================================
% Discrete Lot Sizing problem, CP MODEL
%
% CSPlib Problem 58: http://www.csplib.org/Problems/prob058/
% MIT License
%
% Copyright (c) 2019 Andrea Rendl-Pitrey, Satalia
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
% 
% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.
% 
% Andrea Rendl, July 2019
% ===============================================================================

include "global_cardinality.mzn";
include "alldifferent.mzn";  % for redundant constraint-1
include "at_least.mzn"; % for redundant constraint-2
include "at_most.mzn"; % for redundant constraint-2

int: nb_item_types;   % different item types to produce
int: nb_orders;       % the total number of orders
constraint 
  assert(nb_item_types <= nb_orders, 
         "The number of item types must be greater or equal to the number of total orders.", true);
int: nb_periods;      % time periods available

% cost for inventory for one period of time
int: inventory_cost;

set of int: Orders = 1..nb_orders;
set of int: Orders0 = 0..nb_orders;
set of int: Periods = 1..nb_periods;
set of int: Items = 1..nb_item_types;
set of int: Items0 = 0..nb_item_types;

% the due date of each order
array[Orders] of Periods: due_period;
% the cost of changing from item i to item j
array[Orders0, Orders0] of int: change_cost;
% the number of orders for the item type
array[Items] of int: nb_of_orders;
% maps each order to its item type
array[Orders0] of Items0: item_type; 

% =============== VARIABLES =====================================================

% The sequence of orders that are produced
array[Periods] of var Orders0: production_by_order;
% For each order, the time period in which it is produced
array[Orders] of var Periods: production_period;
% the inventory periods that are required for the production plan 
% (i.e. the number of periods the order is completed before the due date)
array[Orders] of var 0..max(due_period): inventory_periods;
% the change cost for changing the machine setup from period p to p+1
array[1..nb_periods-1] of var 0..max(change_cost): change_cost_for_period;
% the order in which orders are produced
array[Periods] of var Orders0: production_order; 

% =============== CONSTRAINTS ===================================================
                        
% sets the number of times each order has to appear in the production plan
% each order has to be produced exactly once.
constraint 
  global_cardinality(production_by_order, 
                     [ value | value in Orders0], 
                     [ 
                        if order == 0 
                            then nb_periods - nb_orders 
                        else 
                            1
                        endif
                        | order in Orders0]);                                              

% Don't produce the order AFTER its due date
constraint 
   forall (order in Orders) (
      forall (period in Periods where due_period[order] < period) (
           production_by_order[period] != order
      )
   );         


% Linking the production_period variables with the main order variables
constraint 
   forall (order in Orders) (
       production_by_order[production_period[order]] = order
   ); 
% redundant constraint-1   
constraint redundant_constraint(alldifferent(production_period));
   
   
% sets the number of periods that inventory is necessary for each order   
constraint 
   forall(order in Orders) (  
       inventory_periods[order] = due_period[order] - production_period[order]
   );   


% set "production_order" to the order in which items are produced. We will use this variables
% to impose the change_cost constraints   
constraint 
    production_order[1] = production_by_order[1];  
constraint 
    forall (p in 2..nb_periods) (
      if production_by_order[p] == 0 then 
          production_order[p] = production_order[p-1]
      else 
          production_order[p] = production_by_order[p]
      endif
      )
;
% redundant constraints-2 (sometimes they improve performance, sometimes not)
constraint 
   forall(o in Orders) (
      redundant_constraint(at_least(1, production_order, o)) /\
      redundant_constraint(at_most(1 + (nb_periods - nb_orders), production_order, o))
   ); 


% the change cost is applied when changing from one item type to another  
constraint 
   forall (p in 1..nb_periods-1) (
        change_cost_for_period[p] = change_cost[production_order[p], production_order[p+1]]
   );
   
   
% breaking symmetry: complete orders of same type in a fixed order (the ones first are produced first) 
constraint 
  forall(item_type in Items) (
     symmetry_breaking_constraint(
        if nb_of_orders[item_type] > 1 then
        forall(k in 1..(nb_of_orders[item_type]-1)) (
            production_period[order_number(item_type, k)] < production_period[order_number(item_type, k+1)]
        )
     else true 
     endif
     )
  );  
      
  
% returns the order number of the k-th order of item_type  
function int: order_number(Items: item_type, int: k) = 
   if item_type == 1 
     then k
   else 
      sum( [ nb_of_orders[item] | item in 1..item_type-1 ]) + k 
   endif; 


% =============== OBJECTIVE =====================================================

int: upper_bound = max(change_cost)*nb_orders + inventory_cost*(nb_orders*nb_periods);
var 0..upper_bound: objective;

% the objective is the sum of the total change costs and the total inventory costs
constraint 
   objective = sum(p in 1..nb_periods-1) (change_cost_for_period[p]) 
               + sum(o in Orders) (inventory_periods[o]) * inventory_cost;

solve :: seq_search(
                [int_search(production_by_order, first_fail, indomain_median, complete),
                 int_search(inventory_periods, first_fail, indomain_min, complete)])               
  minimize objective;

% Output

output [
    "production_by_order = \(production_by_order);\n",
    "inventory_periods = \(inventory_periods);\n",
    "objective = \(objective);\n"
];

