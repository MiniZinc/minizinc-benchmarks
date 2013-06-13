%-----------------------------------------------------------------------------
% Car sequencing problem
%
% Nina Narodytska
% 01.12.2007
%
% CSPLIB Problem 001:
% "A number of cars are to be produced; they are not identical, 
% because different options are available as variants on the basic model. 
% The assembly line has different stations which install the various options 
% (air-conditioning, sun-roof, etc.). 
% These stations have been designed to handle at most a certain percentage of 
% the cars passing along the assembly line. 
% Furthermore, the cars requiring a certain option must not be bunched together, 
% otherwise the station will not be able to cope. Consequently, the cars must be 
% arranged in a sequence so that the capacity of each station is never exceeded. 
% For instance, if a particular station can only cope with at most half of the 
% cars passing along the line, the sequence must be built so that at most 1 car 
% in any 2 requires that option."
%
% The car sequencing problem example is adapted from the Ilog example. 
% The model of the problem is discussed in details in [1].
%
% [1] J.-C. Regin and J.-F. Puget. A Filtering Algorithm for Global Sequencing 
% Constraints. In CP’97, volume 1330 of LNCS, pages 32–46. Springer, 1997.
%

% To test the model:
%
%  carseq.mzn --data data/test/car_test_1.dzn
%  or
%  carseq.mzn --data data/test/car_test_0.dzn
%-----------------------------------------------------------------------------

include "globals.mzn";

%-------------------------------------------------
% Model parameters
%-------------------------------------------------
int: n_cars;      % The number of cars
int: n_options;   % The number of options to install, e.g "sun roof", "air-conditioning".
int: n_confs;     % The number of configurations. A configuration specifies a variant on the basic model.
                  % e.g. a configuration may include the basic model, sun roof and air-conditioning.

set of int: cars             = 1..n_cars;
set of int: options          = 1..n_options;
set of int: configurations   = 1..n_confs;
set of int: cars_options     = 1..n_cars*n_options;



array [options] of int: k;
array [options] of int: min_caps;       % min_caps[j] --   the minimum capacity of the jth station (the jth station installs jth option).  
array [options] of int: max_caps;       % max_caps[j] --   the maximum capacity of the jth station 

array [configurations]  of int: n_cars_by_confs;        % n_cars_by_confs[j] -- the required number of cars of jth configuration. 
array [configurations, options]  of int: confs;         % if confs[i,j] == 1 then ith option has to be installed for jth configuration

array [options] of int: options_ordering;               % An options ordering: options for which demand is closer to capacity are assigned first. [1]
							

%----------------------------------------------------
% Additional model parameters 
%----------------------------------------------------

% the number of options in each configuration
array [configurations] of int: n_opts_by_confs = [ sum (j in options)( confs[i,j] ) | i in configurations];

% set of configurations for each option 
array[options] of set of int: confs_by_opts = 
[ 
	{i| i in configurations where (confs[i,j] mod 2  = 1)}
	| j in options 
];

%-------------------------------------------------
% Model variables
%-------------------------------------------------

array [cars]    of var configurations:         seq_confs;
array [options, cars]  of var 0..1:            b_seq_confs;
array [cars_options]   of var 0..1:            b_aux_seq_confs;
array [configurations] of var cars:            card_confs;
array [configurations] of var configurations:  value_confs; 				

array [options] of var options:  opts;


%-------------------------------------------------
% Model constraints
%-------------------------------------------------

%------------------------------
% -- cardinality restrictions
%------------------------------

% cardinality restrictions on configurations 
constraint
   forall (j in configurations) (
            card_confs[j] = n_cars_by_confs[j]
    );

% encoding of configurations 
constraint
    forall (j in configurations) (
            value_confs[j] = j
    );

% the required number of cars of each configuration 
constraint
	distribute (card_confs, value_confs, seq_confs);

%-----------------------------------
%--  stations' capacity restrictions
%------------------------------------
% channeling constraints
predicate row_channeling (int: i) = 
	forall (j in cars)  (
		(seq_confs[j] in confs_by_opts[i]) <-> b_seq_confs[i,j] = 1
	);
constraint
	forall (i in options)  (
		(row_channeling (i))
	);

% capacity restrictions for each option
predicate row_sequence (int: i) = 
		sequence ([b_seq_confs[i,j] | j in cars ], k[i], min_caps[i], max_caps[i]);

% capacity restriction		
constraint
	forall (i in options)  (
		(row_sequence (i))
	);
	
%-----------------	
%-- heuristics 
%-----------------
% We use heuristics from [1]. 
% Variable ordering: First assign variables in the middle of the schedule
% Note that variable ordering depends on options ordering


predicate row_heuristics (int: i) =
	let {int: s_partition = n_cars div 2} in 
	(
		forall (j in 1..s_partition) (
			b_aux_seq_confs[(i-1)*n_cars + 2*j - 1] = b_seq_confs[i, s_partition - j + 1] 
			/\
			b_aux_seq_confs[(i-1)*n_cars + 2*j] =  b_seq_confs[i, s_partition + j]			
		)
		/\
		b_aux_seq_confs[i*n_cars] = b_seq_confs[i, n_cars]
	);
		
constraint
	forall (i in options)  (
		(row_heuristics (options_ordering[i]))
	);


solve :: int_search(b_aux_seq_confs, input_order, indomain_min, complete) satisfy;
 

%-------------------------------------------------
% Output
%--------------------------------------------------


output [
"Problem description: \n",
"\t number of cars = ", show(n_cars), "\n",
"\t number of options =  ", show(n_options), "\n",
"\t number of configurations =  ", show(n_confs), "\n",
"\t k =  ", show(k), "\n",
"\t min capacity =  ", show(min_caps), "\n",
"\t max capacity =  ", show(max_caps), "\n",
"\t number of cars in configurations  =  ", show(n_cars_by_confs), "\n",
"\t confs  =   \n \t", show(confs), "\n \n",
"Solution: \n",
"\t cars =   \n \t", show(seq_confs), "\n",
"\t options by cars =   \n \t", show(b_seq_confs), "\n"];

