%------------------------------------------------------------------------------%
% vim: ts=4 sw=4 et wm=0 tw=0
%------------------------------------------------------------------------------%
% Copyright (C) 2009-2014 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%------------------------------------------------------------------------------%
% A model for the rectangle (square) packing problem (RPP).
%
% A RPP of size N consists of N square of size 1x1, 2x2, 3x3, ..., NxN. The 
% optimised variant asked for the smallest rectangle wrt. its area where all
% squares can be placed without overlapping in this rectangle.
%------------------------------------------------------------------------------%

include "cumulative.mzn";
include "diffn.mzn";

%------------------------------------------------------------------------------%
% Model parameters for the squares.
%
    

    % Size of the biggest square.
int: n;
    % All squares from size 1x1, 2x2, to NxN.
set of int: Squares = 1..n;
    % Including the square of size 1 in the search and constraints. The reason
    % for a non-consideration is justified by the observation that it can be
    % placed in any free spot in the rectangle.
bool: Consider_Unit_Square;
    % The fraction of slack for squares
float: slack_frac = 0.3;

array [ Squares ] of int: int_slack = 
    [ floor(slack_frac * int2float(i)) | i in Squares ];

%------------------------------------------------------------------------------%
% Model parameters for the rectangle assuming that its height is smaller than
% or equal to its width.
%
%        +------------------------------------+
%        |                                    |
%        |                                    |
% Height |                                    |
%        |                                    |
%        |                                    |
%        +------------------------------------+
%                        Width
%

    % Upper bound for the width
int: max_width  = sum([ i | i in Squares where i >= (n div 2) + 1 ]);
    % Lower bound for the height
int: min_height = if n mod 2 == 1 then n else n + 1 endif;
    % Lower bound for the width
int: min_area   = sum([ i * i | i in Squares ]);
    % Upper bound for the area
int: max_area   = max_width * min_height;
    % Upper bound for the height
int: max_height = floor( sqrt( int2float( max_area ) ) );
    % Lower bound for the width
int: min_width  = ceil(  sqrt( int2float( min_area ) ) );

%------------------------------------------------------------------------------%
% Model variables.
%

    % X-coordinate of the square's origin (left lower corner)
array [ Squares ] of var 0..max_width : X;
    % Y-coordinate of the square's origin (left lower corner)
array [ Squares ] of var 0..max_height: Y;
    
    % Auxiliary X-variables needed for the search strategy
array [ Squares ] of var 0..max_width : X_div = 
    [   if int_slack[i] < 2 then X[i] else
            let { 
                int: dmax = max_width div int_slack[i],
                var 0..dmax: x
            } in x
        endif
    | i in Squares ];
array [ Squares ] of var 0..max_width : X_rem =
    [   if int_slack[i] < 2 then 0 else
            let { var 0..(int_slack[i] - 1): x } in x
        endif
    | i in Squares ];

    % Auxiliary Y-variables needed for the search strategy
array [ Squares ] of var 0..max_height : Y_div = 
    [   if int_slack[i] < 2 then Y[i] else
            let { 
                int: dmax = max_height div int_slack[i],
                var 0..dmax: y
            } in y
        endif
    | i in Squares ];
array [ Squares ] of var 0..max_height : Y_rem =
    [   if int_slack[i] < 2 then 0 else
            let { var 0..(int_slack[i] - 1): y } in y
        endif
    | i in Squares ];

    % The width  of the rectangle
var min_width ..max_width : Width;
    % The height of the rectangle
var min_height..max_height: Height;
    % The area   of the rectangle
var min_area  ..max_area  : Area;

%-----------------------------------------------------------------------------%
% Predicates.
%

test consider_square( int: i ) =
    (   i > 1
    \/  Consider_Unit_Square == true
    );

%-----------------------------------------------------------------------------%
% Constraints.
%

constraint
    forall( i in Squares where consider_square(i) ) (
        if int_slack[i] < 2 then true else
            X[i] = int_slack[i] * X_div[i] + X_rem[i]
        /\  Y[i] = int_slack[i] * Y_div[i] + Y_rem[i]
        endif
    );

    % Non-overlap constraints between two squares
constraint
    diffn(
        [ X[i] | i in Squares where consider_square(i) ],
        [ Y[i] | i in Squares where consider_square(i) ],
        [   i  | i in Squares where consider_square(i) ],
        [   i  | i in Squares where consider_square(i) ]
    );

    % Constraints on the variables of the rectangle
constraint
            % Height is the smaller side
        Height <= Width
            % Area is equals the product of its sides
    /\  Area = Height * Width;

    % Constraints on the x variables
constraint
            % Squares must be inside the rectangle
        forall( i in Squares where consider_square(i) ) (
            X[i] + i <= Width
        )
            % Ensure a "non-overload" of the height
    /\  cumulative(
            [ X[i] | i in Squares where consider_square(i) ],
            [   i  | i in Squares where consider_square(i) ],
            [   i  | i in Squares where consider_square(i) ],
            Height
        );

    % Constraints on the y variables
constraint
            % Squares must be inside the rectangle
        forall( i in Squares where consider_square(i) ) (
            Y[i] + i <= Height
        )
            % Ensure a "non-overload" of the width
    /\  cumulative(
            [ Y[i] | i in Squares where consider_square(i) ],
            [   i  | i in Squares where consider_square(i) ],
            [   i  | i in Squares where consider_square(i) ],
            Width
        );

    % In the case of non-consideration of the unit square its origin is
    % assigned to (0, 0).
constraint
    if Consider_Unit_Square == false then X[1] = 0 /\ Y[1] = 0 else true endif;


%------------------------------------------------------------------------------%
% Model improvements.
%
    % Symmetry breaking rules
constraint
        2 * X[n] <= (Width  - n) 
    /\  2 * Y[n] <= (Height - n);

    % Empty Strip Dominance Criterion 
    % NOTE: Here only an adaption of it from H. Simonis, B. O'Sullivan, "Search
    %       Strategies for Rectangle Packing"
    %
    % Forbidden gaps for squares between their edges and the border of the
    % rectangle.
array [1..45] of int: fgaps = [0, 2, 3, 2, 3, 3, 3, 3, 4, 4, 
                               4, 5, 5, 5, 5, 5, 5, 6, 6, 6,
                               6, 7, 7, 7, 7, 7, 7, 7, 7, 8,
                               8, 8, 8, 8, 9, 9, 9, 9, 9, 9,
                               9, 9, 9, 9, 10];

    % Forbidden gaps for the x-origin
constraint
    forall( i in Squares where consider_square(i) ) (
        if 2 * fgaps[i] + 2 <= max_width - i then
            let {
                var bool: b_left,
                var bool: b_right
            } in (
                (      b_left    -> X[i] <= 0                    )
            /\  ( not( b_left  ) -> X[i] >              fgaps[i] )
            /\  (      b_right   -> X[i] >= Width - i            )
            /\  ( not( b_right ) -> X[i] <  Width - i - fgaps[i] )
            /\  ( not( b_left  ) \/ not( b_right ) )
            )
        else
            let {
                var bool: b_left
            } in (
                (      b_left   -> X[i] <= 0         )
            /\  ( not( b_left ) -> X[i] >= Width - i )
            )
        endif
    );

    % Forbidden gaps for the y-origin
constraint
    forall( i in Squares where consider_square(i) ) (
        if 2 * fgaps[i] + 2 <= max_height - i then
            let {
                var bool: b_left,
                var bool: b_right
            } in (
                (      b_left    -> Y[i] <= 0                     )
            /\  ( not( b_left  ) -> Y[i] >               fgaps[i] )
            /\  (      b_right   -> Y[i] >= Height - i            )
            /\  ( not( b_right ) -> Y[i] <  Height - i - fgaps[i] )
            /\  ( not( b_left  ) \/ not( b_right ) )
            )
        else
            let {
                var bool: b_left
            } in (
                (      b_left   -> Y[i] <= 0          )
            /\  ( not( b_left ) -> Y[i] >= Height - i )
            )
        endif
    );

%-----------------------------------------------------------------------------%
% Objective.
%

solve
    :: seq_search([
        int_search([ Area, Height ], input_order, indomain_min, complete),
        int_search(
            % Added a Zero so that the array is not empty
            [0] ++ [ Y_div[n + 1 - i] | i in Squares where consider_square(n + 1 - i) /\ int_slack[n + 1 - i] > 1],
            input_order, indomain_min, complete
        ),
        int_search(
            [ Y[n + 1 - i] | i in Squares where consider_square(n + 1 - i) ],
            input_order, indomain_split, complete
        ),
        int_search(
            % Added a Zero so that the array is not empty
            [0] ++ [ X_div[n + 1 - i] | i in Squares where consider_square(n + 1 - i) /\ int_slack[n + 1 - i] > 1],
            input_order, indomain_min, complete
        ),
        int_search(
            [ X[n + 1 - i] | i in Squares where consider_square(n + 1 - i) ],
            input_order, indomain_split, complete
        )
    ])
    satisfy;

%-----------------------------------------------------------------------------%
% Output.
%

output [
    "Area = ", show(Area), ";\n",
    "Height = ", show(Height), ";\n",
    "Width = ", show(Width), ";\n",
    "X = ", show(X), ";\n",
    "Y = ", show(Y), ";\n"
];
