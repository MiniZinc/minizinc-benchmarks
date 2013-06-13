% A model for minimal height table layout (in lines)
% given a fixed pixel width
% with some minimum height reasoning!

int: pixelwidth; % pixel width for layout
int: maxconfig;  % maximum configurations per cell
int: rows; % number of rows
int: cols; % number of cols
set of int: ROWS = 1..rows;
set of int: COLS = 1..cols;
set of int: CONFIGS = 1..maxconfig;

array[ROWS,COLS,CONFIGS] of int: width;  % width[r,c,l] in pixels of cell (r,c) in configuration l
				         % padded with 0 to indicate too many configs
array[ROWS,COLS,CONFIGS] of int: height; % height[r,c,l] in pixels of cell (r,c) in configuration l
				         % padded with 0 to indicate too many configs
int: mincellwidth = min([ width[r,c,l] | r in ROWS, c in COLS, l in CONFIGS where width[r,c,l] >= 0 ]);
int: maxcellwidth = max([ width[r,c,l] | r in ROWS, c in COLS, l in CONFIGS ]);										
int: mincellheight = min([ height[r,c,l] | r in ROWS, c in COLS, l in CONFIGS where height[r,c,l] >= 0 ]);
int: maxcellheight = max([ height[r,c,l] | r in ROWS, c in COLS, l in CONFIGS ]);										
array[ROWS,COLS] of int: mincellarea = 
	array2d(ROWS,COLS,[ min( [ height[r,c,l]*width[r,c,l] | 
				 l in CONFIGS where width[r,c,l] >= 0]) |
		r in ROWS, c in COLS ]); 

%array[ROWS] of int: minrowheight = [ sum(c in COLS)(mincellarea[r,c]) div pixelwidth | r in ROWS];

int: maxheight = rows * maxcellheight; % maximum height in pixels
										
% variables 
array[ROWS,COLS] of var CONFIGS: config;

array[ROWS,COLS] of var mincellwidth..maxcellwidth: cellwidth;
array[ROWS,COLS] of var mincellheight..maxcellheight: cellheight;

array[ROWS] of var mincellheight..maxcellheight: rowheight;
array[COLS] of var mincellwidth..maxcellwidth: colwidth;

var mincellheight..maxheight: totalheight = sum(r in ROWS)(rowheight[r]);	


constraint pixelwidth >= sum(c in COLS)(colwidth[c]);

constraint forall(r in ROWS, c in COLS)(
			   rowheight[r] >= cellheight[r,c] 
			/\ colwidth[c] >= cellwidth[r,c]
%			/\ cellheight[r,c] * cellwidth[r,c] >= mincellarea[r,c]
			/\ cellwidth[r,c] == width[r,c,config[r,c]]
			/\ cellheight[r,c] == height[r,c,config[r,c]]); 

% solve :: int_search([config[r,c] | r in ROWS, c in COLS], dom_w_deg, indomain_min, complete)
% solve :: int_search([config[r,c] | r in ROWS, c in COLS], input_order, indomain_min, complete)
solve :: int_search([config[r,c] | r in ROWS, c in COLS], first_fail, indomain_min, complete)
	  minimize totalheight;

output ["(" ++ show(cellheight[r,c]) ++ ","++ show(cellwidth[r,c]) ++ ")" ++ if c == cols then "\n" else " " endif |
		 r in ROWS, c in COLS] ++ 
	   ["totalheight = ",show(totalheight), "\n"];

% data



