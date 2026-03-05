/*
Optimisation of Australian capital gains tax

Written by Jason Nguyen

MIT Licence

Copyright 2025 Monash University
 
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

include "globals.mzn";

enum TRADE = { Buy, Sell };

% Stocks in portfolio
enum STOCK;

% The trades which occurred
array [int] of record(
  int: date,
  TRADE: trade,
  STOCK: stock,
  int: units,
  int: price
): trades;

int: UNIT_BUY_COUNT = count (x in trades, i in 1..x.units) (x.trade = Buy);
int: UNIT_SELL_COUNT = count (x in trades, i in 1..x.units) (x.trade = Sell);

enum UNIT_BUY = UnitBuy(1..UNIT_BUY_COUNT);
enum UNIT_SELL = UnitSell(1..UNIT_SELL_COUNT);

any: unit_buys = array1d(UNIT_BUY, [(date: x.date, stock: x.stock, price: x.price) | x in trades where x.trade = Buy, i in 1..x.units]);
any: unit_sells = array1d(UNIT_SELL, [(date: x.date, stock: x.stock, price: x.price) | x in trades where x.trade = Sell, i in 1..x.units]);

% The bought unit which was sold
array [UNIT_SELL] of var UNIT_BUY: origin;

% Cannot sell the same unit twice
constraint all_different(origin);
% Must have bought the unit before selling
constraint forall (u in UNIT_SELL) (unit_buys[origin[u]].date < unit_sells[u].date);
% Order of origins doesn't matter for a fungible units
constraint forall (t in trades where t.trade = Sell) (
  symmetry_breaking_constraint(
    strictly_increasing (u in UNIT_SELL, x = unit_sells[u] where t.date = x.date /\ t.stock = x.stock /\ t.price = x.price) (origin[u])
  )
);

% Eligible for 50% discount if held for >= 12 months
any: discountable_gains = sum (u in UNIT_SELL, sale = unit_sells[u], bought = unit_buys[origin[u]] where sale.date - bought.date >= 12 /\ sale.price > bought.price) (
    sale.price - bought.price
);
% Not eligible for discount
any: undiscountable_gains = sum (u in UNIT_SELL, sale = unit_sells[u], bought = unit_buys[origin[u]] where sale.date - bought.date < 12 /\ sale.price > bought.price) (
    sale.price - bought.price
);
% Capital losses
any: losses = sum (u in UNIT_SELL, sale = unit_sells[u], bought = unit_buys[origin[u]] where sale.price < bought.price) (
    bought.price - sale.price
);

% The taxable capital gains x2
any: double_capital_gains =
  if undiscountable_gains > losses then
    discountable_gains + 2 * undiscountable_gains - 2 * losses
  elseif losses - undiscountable_gains < discountable_gains then
    discountable_gains - (losses - undiscountable_gains)
  else
    2 * (discountable_gains + undiscountable_gains - losses)
  endif;

% Minimize capital gains
var int: objective :: output = double_capital_gains;
solve :: int_search(origin, input_order, indomain_min) minimize objective;
