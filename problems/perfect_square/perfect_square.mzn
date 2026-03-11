%
% Model for perfect square
%
%

% This models perfect square problem (also called squared square problem).
% it is described in "A Note on Perfect Square Placement" by N. Beldiceanu
% E. Bourreau and H. Simonis.
% The data to this model are copied from the above paper.

% ------------------------------------------------------------------------------
% Copyright 2021 Krzysztof Kuchcinski

% Permission is hereby granted, free of charge, to any person obtaining a copy of
% this software and associated documentation files (the "Software"), to deal in
% the Software without restriction, including without limitation the rights to use,
% copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
% and to permit persons to whom the Software is furnished to do so, subject to the
% following conditions:

% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.

% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
% INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
% PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
% HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
% CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
% OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
% ------------------------------------------------------------------------------

include "globals.mzn";

int: n;                     % number squars
int: size;                  % size of the square to fill with n squars
array[1..n] of int: squars; % dimension of the squares

array[1..n] of var 0..size: x; % x poition of squars
array[1..n] of var 0..size: y; % y poition of squars

constraint
   forall(i in 1..n) (
      x[i] <= size - squars[i]
      /\
      y[i] <= size - squars[i]
   )
   /\
   diffn(x, y, squars, squars)
;

solve :: seq_search([
      int_search([x[n-i+1] | i in 1..n], smallest, indomain_min, complete),
      int_search([y[n-i+1] | i in 1..n], smallest, indomain_min, complete)
      ]) satisfy;

output[show(x)] ++ ["\n"] ++ [show(y)];

