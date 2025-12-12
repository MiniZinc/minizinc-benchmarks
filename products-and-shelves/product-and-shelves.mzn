% ------------------------------------------------------------------------------
% Copyright 2025 Ericsson
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the “Software”), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.
% ------------------------------------------------------------------------------
%% Author: Danyal Mirza danyal.mirza@ericsson.com
%% Problem description:
% In a warehouse, a number of products are to be placed on some shelves such that
% the the minimum amount of shelves are used. These products are all shaped like
% 3-dimensional boxes, with dimensions length, width and height. The shelves are
% also shaped like 3-dimensional boxes with dimensions length, width and height
% and the number of shelves are finite. Neither the shelf or the products are
% allowed to be rotated.
%
%            +--------------+
%           /|             /|
%          / |            / |
%         *--+-----------*  |
%         |  |           |  |
% height->|  |           |  |
%         |  |           |  |
%         |  +-----------+--+
%         | / <-width    | /
%         |/             |/
%         *--------------*
%             length^

% Modifications by MiniZinc Challenge Organizers:
% - Add integer `objective' variable

include "diffn_nonstrict_k.mzn";
include "increasing.mzn";
include "lex_chain_lesseq.mzn";
include "seq_precede_chain.mzn";

% Dimensions considered
enum Dimension = {Length, Width, Height};

%% Parameters
enum Product;

% Space available on each shelf in all dimensions
array[Dimension] of int: shelves;
% Space required for each product in all dimensions
array[Product, Dimension] of int: product_size;
% Total number of shelves
int: nr_shelves;

%% Derived Parameters
enum Shelf = S(1..nr_shelves);
% Number of each product
array[Product] of int: nr_products;
% Enumeration of all items (of all type products)
enum Item = I(1..sum(nr_products));
% Mapping each item to its product
array[Item] of Product: product = array1d(Item, [
	p | p in Product, _ in 1..nr_products[p]
]);

%% Decsision Variables
% The size of each product is its size if it is in the shelf and [0, 0, 0] if it is not
array[Item, Shelf, Dimension] of var 0..max(product_size): item_shelve_size ::output;
% Product j is placed on shelf item_shelving[j]
array[Item] of var Shelf: item_shelving ::output;
% Starting positions of each product in each shelf
array[Item, Shelf, Dimension] of var 0..max(shelves): item_shelve_placement ::output;
% The number of loaded shelves is the max item_shelving, this will also force
% shelves to be filled in ascending order, starting from 1
var Shelf: last_loaded_shelf ::output = max(item_shelving);

% Sets all rows in products_sizes_3d to their respective sizes if they exist in
% shelf i and [0, 0, 0] if they do not exist in shelf i
constraint forall(s in Shelf, it in Item, p = product[it]) (
	if item_shelving[it] == s then
		item_shelve_size[it, s, ..] = product_size[p,..]
	else
		item_shelve_size[it, s, ..] = [0, 0, 0]
	endif
);

% Constrains all products in each shelf to no overlap, nonstrict is used so
% that we do not include products which are not in that shelf (they have sizes
% [0, 0, 0])
constraint forall(s in Shelf) (
	diffn_nonstrict_k(item_shelve_placement[.., s, ..], item_shelve_size[.., s, ..])
);

% The products must be placed such that they are contained within the dimensions of
% the shelf
constraint forall(s in Shelf, it in Item, d in Dimension) (
	item_shelve_placement[it, s, d] + item_shelve_size[it, s, d] <= shelves[d]
);

% Break symmetry of between the different shelves
constraint symmetry_breaking_constraint(
	seq_precede_chain(item_shelving)
);

% Break symmetry of shelving of multiple of the same products
constraint symmetry_breaking_constraint(
	forall(p in Product) (
		increasing([item_shelving[it] | it in Item where product[it] == p])
	)
);

% Break symmetry between placement of the same products
constraint symmetry_breaking_constraint(
	forall(s in Shelf, p in Product) (
		let {
			% Note that this works because `i` is gauranteed to form a continues
			% sequence because of how `Item` is created.
			any: coord =
			  [ (d, i): item_shelve_placement[i, s, d]
			  | i in Item where product[i] == p, d in Dimension];
		} in lex_chain_lesseq(coord)
	)
);

var int: objective :: output = enum2int(last_loaded_shelf);

solve :: seq_search([
			int_search(item_shelve_size, first_fail, indomain_min, complete),
			int_search(item_shelve_placement, first_fail, indomain_min, complete)
		])
minimize objective;

% % Output
% % Real placement
% array[Item] of any: item_placement ::output_only ::output = [
% 	(p[Length], p[Width], p[Height])
% 	| it in Item, p = fix(item_shelve_placement[it, fix(item_shelving[it]), ..])
% ];

% % Output code to check the placement on all (potentially unused shelves)
% output [
% 	show2d([(d, i): item_shelve_placement[i, s, d] | i in Item where product[i] = p, d in Dimension]) ++ "\n"
% 	| s in Shelf, p in Product,
% ]
