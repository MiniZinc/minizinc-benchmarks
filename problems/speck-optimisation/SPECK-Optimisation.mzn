% Copyright 2023 David Gerault

% Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

% The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

% THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


include "globals.mzn";

int: n; % Word size
int: nr; % Number of rounds

% Rotational constants
int: lr = if n = 16 then 2 else 3 endif; % left rotation value
int: rr = if n = 16 then 7 else 8 endif; % right rotation value

% The 2 words of the state
array [0..nr, 0..n-1] of var bool: L :: output;
array [0..nr, 0..n-1] of var bool: R :: output;

% The probability vector
array [0..nr-1] of var 0..n: p :: output;

var 0..n*4: objective :: output = sum(p);

% Non-zero difference
constraint sum(row(L, 0) ++ row(R, 0)) > 0;

% Round function
constraint forall(i in 0..nr-1)(
    modular_addition_word(RRot(row(L, i), rr), row(R ,i), row(L, i+1), p[i]) /\
    row(R, i + 1) = XOR(row(L, i + 1), LRot(row(R, i), lr))
);

predicate modular_addition_word(
  array[0..n-1] of var bool: a,
  array[0..n-1] of var bool: b,
  array[0..n-1] of var bool: c,
  var 0..n-1: p
) = (
    let {
        array [0..n-1] of var bool: carry_difference
    } in   
    carry_difference[n-1] = 0 /\
    forall (i in 0..n-1) (
      (a[i] xor b[i] xor carry_difference[i] xor c[i]) = 0
    ) /\
    forall (i in 1..n-1) (
      all_equal([a[i], b[i], c[i]]) -> all_equal([a[i], b[i], c[i], carry_difference[i - 1]])
    ) /\
    p = count (i in 1..n-1) (not all_equal([a[i], b[i], c[i], carry_difference[i], carry_difference[i - 1]]))
);

function array [0..n-1] of var bool: LRot(array[0..n-1] of var bool: X, int: val) =
  [j: X[(j + val) mod n] | j in 0..n-1];

function array [0..n-1] of var bool: RRot(array[0..n-1] of var bool: X, int: val) =
  [j: X[(n + j - val) mod n] | j in 0..n-1];

function array [0..n-1] of var bool: XOR(array[0..n-1] of var bool: a, array[0..n-1] of var bool: b) =
  [j: XORbits([a[j], b[j]]) | j in 0..n-1];

function array [0..n-1] of var bool: XOR(
  array[0..n-1] of var bool: a,
  array[0..n-1] of var bool: b,
  array[0..n-1] of var bool: c
) = [j: XORbits([a[j], b[j], c[j]]) | j in 0..n-1];

function array [0..n-1] of var bool: XOR(
  array[0..n-1] of var bool: a,
  array[0..n-1] of var bool: b,
  array[0..n-1] of var bool: c,
  array[0..n-1] of var bool: d
) = [j: XORbits([a[j], b[j], c[j], d[j]]) | j in 0..n-1];

function var bool: XORbits(array [int] of var bool: X)=
  xorall(X);

solve 
  :: seq_search([
       int_search(p, input_order, indomain_min),
       bool_search(L, input_order, indomain_min),
       bool_search(R, input_order, indomain_min),
     ])
minimize objective;
