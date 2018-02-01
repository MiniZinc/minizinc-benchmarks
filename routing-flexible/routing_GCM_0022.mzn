/*
 * An automatic MiniZinc model
 */

int: nCostSupport0 = 300000;
int: nDSf_Pi2Pi = 1;
int: nLengthUnitMM = 100;	 %%% Discr unit length in mm

var 649..649: nXNd__1_1_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 92..92: nXNd__1_1_Y;
var 145..145: nXNd__1_1_Z;
var -30..748: nXNd__1_2_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_2_Y;
var 0..430: nXNd__1_2_Z;
var -30..748: nXNd__1_3_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_3_Y;
var 0..430: nXNd__1_3_Z;
var -30..748: nXNd__1_4_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_4_Y;
var 0..430: nXNd__1_4_Z;
var -30..748: nXNd__1_5_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_5_Y;
var 0..430: nXNd__1_5_Z;
var -30..748: nXNd__1_6_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_6_Y;
var 0..430: nXNd__1_6_Z;
var -30..748: nXNd__1_7_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_7_Y;
var 0..430: nXNd__1_7_Z;
var -30..748: nXNd__1_8_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_8_Y;
var 0..430: nXNd__1_8_Z;
var -30..748: nXNd__1_9_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 33..320: nXNd__1_9_Y;
var 0..430: nXNd__1_9_Z;
var 650..650: nXNd__1_10_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 54..54: nXNd__1_10_Y;
var 15..15: nXNd__1_10_Z;

array[int] of int: nBoxType = [1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4, 5, 5, 5, 5, 5, 3, ];
array[int] of int: nXBx_1D = [0, 176, 70, 1, 173, 67, 15, 173, 71, 19, 173, 95, 32, 150, 160, 68, 40, 0, 105, 223, 126, 107, 223, 124, 116, 223, 142, 116, 225, 140, 116, 268, 7, 118, 223, 149, 118, 268, 5, 125, 223, 151, 126, 78, 10, 126, 80, 30, 128, 157, 30, 135, 157, 7, 135, 159, 5, 156, 78, 10, 156, 80, 30, 158, 235, 30, 233, 117, 32, 233, 119, 30, 235, 117, 324, 239, 98, 99, 239, 102, 95, 243, 98, 346, 248, 74, 0, 218, 44, 0, 272, 98, 334, 303, 98, 72, 303, 100, 23, 320, 102, 23, 320, 103, 150, 320, 192, 25, 322, 101, 150, 325, 102, 72, 325, 270, 76, 329, 270, 90, 334, 88, 0, 304, 58, 0, 347, 79, 52, 349, 77, 52, 368, 105, 115, 375, 71, 115, 377, 71, 113, 377, 71, 177, 377, 223, 2, 379, 223, 0, 400, 70, 0, 400, 120, 84, 375, 95, 59, 410, 58, 200, 385, 33, 175, 417, 105, 60, 417, 105, 60, 417, 152, 87, 417, 152, 102, 417, 162, 60, 417, 164, 87, 417, 164, 102, 418, 103, 10, 418, 105, 30, 418, 93, 10, 418, 95, 65, 420, 169, 65, 420, 170, 30, 422, 115, 229, 423, 71, 179, 423, 104, 192, 423, 106, 190, 423, 152, 67, 423, 154, 65, 423, 164, 104, 423, 166, 123, 423, 223, 2, 425, 115, 238, 425, 147, 190, 425, 161, 65, 440, 77, 54, 440, 79, 87, 442, 104, 127, 442, 106, 125, 442, 154, 102, 442, 248, 104, 444, 104, 360, 449, 102, 172, 449, 105, 169, 449, 115, 172, 452, 102, 223, 456, 105, 241, 456, 147, 192, 458, 103, 241, 460, 73, 113, 462, 103, 113, 466, 71, 115, 466, 163, 65, 468, 71, 113, 468, 71, 177, 470, 86, 0, 440, 56, 0, 487, 103, 400, 487, 106, 409, 487, 151, 128, 487, 154, 125, 490, 124, 286, 490, 148, 60, 490, 148, 60, 490, 160, 60, 490, 163, 125, 508, 104, 163, 508, 102, 223, 508, 103, 113, 508, 103, 241, 508, 104, 87, 514, 73, 113, 516, 104, 32, 516, 106, 30, 516, 105, 241, 516, 147, 192, 518, 147, 190, 522, 102, 172, 522, 105, 169, 522, 115, 172, 525, 115, 238, 538, 58, 200, 513, 33, 175, 538, 92, 0, 513, 67, 0, 550, 115, 229, 551, 71, 179, 551, 104, 192, 551, 106, 190, 558, 106, 5, 558, 106, 30, 558, 162, 30, 568, 105, 5, 576, 221, 60, 578, 105, 5, 580, 217, 60, 580, 279, 60, 581, 105, 214, 581, 270, 94, 585, 101, 214, 590, 192, 120, 592, 190, 120, 592, 208, 120, 598, 105, 5, 598, 150, 160, 616, 105, 95, 616, 105, 85, 620, 46, 0, 630, 53, 15, 636, 92, 0, 606, 62, 0, 645, 101, 202, 649, 72, 185, 662, 105, 40, 662, 101, 171, 662, 104, 106, 663, 92, 30, 663, 160, 30, 663, 92, 30, 670, 106, 106, 670, 190, 108, 670, 187, 128, 671, 208, 122, 673, 187, 125, 680, 279, 41, 682, 166, 125, 684, 279, 37, 687, 101, 64, 687, 105, 60, 692, 84, 0, 696, 106, 15, 696, 92, 15, 700, 282, 40, -30, 130, 0, 0, 160, 0, 0, 160, 30, 0, 160, 60, 0, 160, 90, 0, 160, 120, -30, 33, 0, ];
array[int] of int: nSzBx_1D = [1, 1, 1, 18, 8, 8, 8, 8, 28, 224, 8, 8, 170, 150, 25, 150, 80, 10, 4, 4, 34, 272, 4, 4, 5, 5, 9, 5, 45, 5, 5, 5, 135, 9, 5, 5, 19, 5, 5, 5, 5, 9, 5, 5, 22, 5, 79, 5, 9, 5, 5, 5, 5, 25, 5, 111, 5, 5, 5, 22, 5, 157, 5, 77, 5, 5, 5, 5, 294, 5, 118, 5, 13, 5, 5, 8, 8, 251, 8, 75, 8, 33, 8, 8, 55, 55, 334, 115, 115, 364, 8, 8, 16, 26, 8, 8, 19, 5, 5, 5, 92, 5, 5, 91, 5, 5, 5, 127, 12, 5, 5, 8, 172, 8, 8, 8, 18, 256, 8, 8, 35, 35, 175, 95, 95, 205, 5, 9, 5, 93, 5, 5, 49, 1, 1, 4, 4, 64, 85, 4, 4, 48, 4, 4, 4, 4, 124, 46, 4, 4, 40, 60, 10, 17, 80, 27, 67, 130, 77, 29, 205, 29, 79, 255, 79, 1, 1, 55, 1, 57, 1, 8, 4, 4, 27, 4, 4, 141, 1, 1, 25, 5, 5, 8, 4, 4, 5, 5, 22, 5, 67, 5, 4, 4, 57, 4, 76, 4, 48, 4, 4, 98, 5, 5, 6, 6, 12, 4, 4, 21, 4, 4, 8, 4, 43, 4, 4, 4, 22, 4, 9, 4, 4, 4, 21, 4, 59, 4, 4, 4, 123, 27, 6, 6, 33, 4, 4, 43, 4, 4, 5, 5, 35, 5, 87, 5, 4, 4, 235, 4, 144, 4, 4, 96, 4, 4, 4, 23, 26, 4, 4, 6, 6, 54, 6, 13, 6, 6, 6, 69, 18, 6, 6, 4, 44, 4, 4, 4, 51, 12, 4, 4, 4, 32, 4, 8, 4, 4, 4, 4, 64, 4, 8, 4, 48, 4, 4, 85, 4, 4, 38, 38, 400, 98, 98, 430, 6, 6, 12, 6, 48, 6, 6, 6, 284, 6, 12, 6, 1, 24, 1, 1, 1, 226, 1, 12, 1, 173, 1, 1, 195, 6, 6, 21, 1, 1, 17, 6, 6, 8, 4, 4, 10, 4, 4, 10, 5, 5, 4, 32, 4, 5, 5, 57, 5, 66, 5, 4, 44, 4, 4, 4, 51, 35, 4, 4, 6, 6, 54, 6, 13, 6, 6, 6, 69, 28, 6, 6, 29, 205, 29, 79, 255, 79, 68, 27, 5, 118, 77, 30, 6, 6, 12, 4, 4, 21, 4, 4, 8, 4, 43, 4, 1, 1, 25, 1, 56, 1, 1, 1, 30, 1, 1, 21, 8, 62, 8, 1, 1, 21, 111, 8, 8, 104, 8, 8, 8, 169, 8, 8, 8, 124, 64, 8, 8, 5, 18, 5, 80, 5, 5, 81, 5, 5, 1, 1, 21, 150, 100, 25, 21, 1, 1, 21, 1, 1, 40, 15, 15, 1, 1, 21, 26, 26, 202, 86, 86, 232, 8, 8, 16, 1, 21, 1, 21, 1, 1, 29, 8, 8, 10, 5, 5, 1, 68, 1, 1, 1, 30, 33, 1, 1, 5, 86, 5, 5, 5, 14, 6, 6, 32, 5, 5, 38, 12, 6, 6, 8, 8, 23, 6, 24, 6, 16, 8, 8, 8, 8, 111, 8, 116, 8, 8, 30, 15, 1, 1, 21, 1, 1, 15, 1, 1, 1, 760, 190, 160, 700, 130, 5, 700, 130, 5, 700, 130, 5, 700, 130, 5, 700, 130, 5, 778, 287, 30, ];
array[int] of int: nDSf2Pi = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, ];
array[int] of int: nBoxCostSupport = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 300000, 0, 0, 0, 0, 0, 300000, ];
array[int] of int: nNodePipe = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ];
array[int] of int: nDiam = [1, ];
array[int] of int: fThruRack = [0, ];
array[int] of int: nLLeg_LB = [2, ];
array[int] of int: nLLeg_UB = [778, ];
array[int] of int: nDirNz1 = [5, ];
array[int] of int: nDirNz2 = [6, ];
array[int] of int: nLLegNz1_LB = [2, ];
array[int] of int: nLLegNz1_UB = [60, ];
array[int] of int: nLLegNz2_LB = [2, ];
array[int] of int: nLLegNz2_UB = [60, ];
array[int] of int: nNz1ModuleBox = [155, ];
array[int] of int: nNz2ModuleBox = [153, ];
array[int] of int: nCostPipePerLenUnit = [3000, ];
array[int] of int: nCostBend = [30000, ];
	 %%% The C'' constants for each pipe: E * D(in) / 48 / S_A
array[int] of float: dGCM_Cpp = [6.863592917937281, ];

array[int] of var int: nXNd_1D = [nXNd__1_1_X, nXNd__1_1_Y, nXNd__1_1_Z, nXNd__1_2_X, nXNd__1_2_Y, nXNd__1_2_Z, nXNd__1_3_X, nXNd__1_3_Y, nXNd__1_3_Z, nXNd__1_4_X, nXNd__1_4_Y, nXNd__1_4_Z, nXNd__1_5_X, nXNd__1_5_Y, nXNd__1_5_Z, nXNd__1_6_X, nXNd__1_6_Y, nXNd__1_6_Z, nXNd__1_7_X, nXNd__1_7_Y, nXNd__1_7_Z, nXNd__1_8_X, nXNd__1_8_Y, nXNd__1_8_Z, nXNd__1_9_X, nXNd__1_9_Y, nXNd__1_9_Z, nXNd__1_10_X, nXNd__1_10_Y, nXNd__1_10_Z, ];


/* Pipe routing submodel
 *
 * TODO  Combine with modules?
 * TODO  Ensure 3D element is linearized well
 * Problem: nozzle legs should go INTO their modules.....?
 * Put future pipe nozzles as fixed boxes, removing them before their pipe
 * TODO  CANNOT GO THROUGH PREFERRED RACK LEVEL BASE
 * 
 * CARE with operator precedence. <->, ->, <-, \/, xor, /\, </ >, <=, >=, ...
 * Say b <-> x in a..b instead of b <-> ( x>=a /\ x<=b ) ??
 */

/*
 * SIMPLIFYING
 * Just ensure every node is in a module's 3m zone or 2-3m above ground
 * No leg between disjoint zones ??
 * Into the rack, nozzles can go as far as 6m !!! ???
 * Lower support costs in rack preferred levels - make sure they are disjoint
 * Now they are 0 - nNodeCstSp can be simplified    TODO
 */

/* INPUT
 * - nNodePipe, array of each Node's pipe number, 11111122222222 etc.
 * - nBoxType, for each fixed box: 1-module, 2- fixed pipe leg,
 *     3-module's support zone, 4-rack big,
 *     5-rack pref level (all latter disj and in a bigger rack)
 * - nDSf2Pi, each box' safety distance to pipes
 * - nDSf_Pi2Pi
 * - nDiam, each pipe's diameter
 * - fNoPockets[], flag for each pipe    TODO
 * - fThruRack[], if the pipe has to make a bend on a rack, to avoid going straight over modules
 * - nLLeg_LB[], nLLeg_UB[] per pipe
 * - nDirNz1[], nDirNz2[] (incoming dir for nz2)  for each pipe     TODO variable nozzle dir
 * - nLLegNz1_LB, nLLegNz1_UB, nLLegNz2_LB, nLLegNz2_UB for each pipe
 * - nNz1ModuleBox, nNz2ModuleBox for each pipe
 * - nCostPipePerLenUnit[]
 * - nCostBend[]
 * - nCostSupport0, default support cost per bend
 * - nBoxCostSupport[], support cost in a box, taken only for pref rack levels which should be disjoint
 * 
 * - nLengthUnitMM
 * - dGCM_Cpp[], the flexibility constraint factor for each pipe
 * 
 * - nXBx_1D, nSzBx_1D, fixed boxes' coords & sizes
 * 
 * - nXNd_1D, coord variables for the nodes, organized in a single linear array[1..3n]
 *       ( each pipe's ends fixed )
 */


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% BASIC SETS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
set of int: TCOORDS = 1..3;
set of int: TBOXES = index_set( nBoxType );
set of int: T_RACKS = { i | i in TBOXES where 4==nBoxType[i] };
set of int: T_RACKPREFLEVELS = { i | i in TBOXES where 5==nBoxType[i] };
set of int: TSUPPORTS = { i | i in TBOXES where 3<=nBoxType[i] };
set of int: TPIPES = index_set( nDiam );
set of int: TPIPENODES = 1..length( nXNd_1D ) div length( TCOORDS );        %% for all pipes
constraint assert( length( TPIPENODES ) * length( TCOORDS ) == length( nXNd_1D ), "ERR 01" );
set of int: TPIPELEGS_RANGE = TPIPENODES;
test isActualLeg( TPIPELEGS_RANGE: iL ) =
                          ( iL<length( TPIPELEGS_RANGE ) /\ nNodePipe[iL+1]==nNodePipe[iL] );
set of int: TPIPELEGS = { i | i in TPIPELEGS_RANGE where isActualLeg(i) };
%%% For each pipe, the 1st leg is always the 1st in the list
%%% (The last leg is dynamic, see fLastLeg[])
test isFirstLeg( TPIPELEGS_RANGE: iL ) = ( 1==iL \/ nNodePipe[iL-1] != nNodePipe[iL] );
test isLastPossLeg( TPIPELEGS: iL ) = ( not isActualLeg(iL+1) );
array[int] of set of int: TPIPELEGS_BYPIPE = [ { i | i in TPIPELEGS where p==nNodePipe[i] } | p in TPIPES ];
array[int] of int: nPipeLeg1st = [ min( TPIPELEGS_BYPIPE[iP] ) | iP in TPIPES ];
array[int] of int: nPipeLegLast = [ max( TPIPELEGS_BYPIPE[iP] ) | iP in TPIPES ];
%% set of int: TCOSTCLASSES = index_set( nCCCost );

int: nOBJCOEFDIVISOR = 100;     %% For Gurobi 6.5, even 1000


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%% TRANSFORMING 1D->N-D DATA ARRAYS %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[int, int] of int: nXBx = array2d( TBOXES, TCOORDS, nXBx_1D );
array[int, int] of int: nSzBx = array2d( TBOXES, TCOORDS, nSzBx_1D );
array[int, int] of int: nXBx2 = array2d( TBOXES, TCOORDS,                      %% The upper-far-right corner
                                         [ nXBx_1D[ik] + nSzBx_1D[ik] | ik in index_set( nXBx_1D ) ] );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%% TRANSFORMING OTHER DATA %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%array[int] of int: nPipeLastNodeIndices_0 =
%%  array1d( 0..length( nPipeLastNodeIndices ), [ 0 ] ++ nPipeLastNodeIndices );
%%constraint assert( nPipeLastNodeIndices[ length( nPipeLastNodeIndices ) ] == length( TPIPENODES ) );

array[int] of int: nRadius = [ nDiam[i] div 2 | i in TPIPES ];

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%% TRANSFORMING / CREATING VAR ARRAYS %%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[int, int] of var int: nXNd = array2d( TPIPENODES, TCOORDS, nXNd_1D );

%% A leg's boundaries in dim k. Sorted for each leg. Connecting to leg lengths
array[TPIPELEGS_RANGE, TCOORDS] of var int: nXLeg1;
array[TPIPELEGS_RANGE, TCOORDS] of var int: nXLeg2;
%% A leg's length in dim k.
array[TPIPELEGS_RANGE, TCOORDS] of var 0..max( nLLeg_UB ): nLLeg;    %% Adding >=0 for pow()
%% A leg's direction flags, 0: zero, 1..3: positive, 4..6: negative.
array[TPIPELEGS_RANGE] of var 0..6: nDirLeg;
%% A leg's existence and 'being last' flags
array[TPIPELEGS_RANGE] of var 0..1: fExistLeg;
array[TPIPELEGS_RANGE] of var 0..1: fLastLeg;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% First, set variable bounds / fix
constraint forall( iL in TPIPELEGS_RANGE, k in TCOORDS )(
  if not isActualLeg( iL ) then
    nXLeg1[iL,k]==0 /\ nXLeg2[iL,k]==0
    /\ nDirLeg[iL]==0 /\ nLLeg[iL,k]==0 /\ fExistLeg[iL]==0 /\ fLastLeg[iL]==0
  else
       nXLeg1[iL,k] >= min( lb( nXNd[iL,k] ), lb( nXNd[iL+1,k] ) ) - nRadius[ nNodePipe[iL] ]
    /\ nXLeg1[iL,k] <= max( ub( nXNd[iL,k] ), ub( nXNd[iL+1,k] ) ) - nRadius[ nNodePipe[iL] ]
    /\ nXLeg2[iL,k] >= min( lb( nXNd[iL,k] ), lb( nXNd[iL+1,k] ) ) + nRadius[ nNodePipe[iL] ]
    /\ nXLeg2[iL,k] <= max( ub( nXNd[iL,k] ), ub( nXNd[iL+1,k] ) ) + nRadius[ nNodePipe[iL] ]
    /\    %%% LEG LENGTH >= 0
       nLLeg[iL,k] >= 0
    /\
       if isFirstLeg(iL) then
         nDirLeg[iL] == nDirNz1[ nNodePipe[iL] ]
         /\
         if k==(nDirNz1[ nNodePipe[iL] ]-1) mod 3 + 1 then
           nLLeg[iL,k] >= nLLegNz1_LB[ nNodePipe[iL] ] /\ nLLeg[iL,k] <= nLLegNz1_UB[ nNodePipe[iL] ]
         else
           nLLeg[iL,k] == 0
         endif
       elseif isLastPossLeg(iL) then
         nDirLeg[iL] in {0,nDirNz2[ nNodePipe[iL] ]}
         /\
         if k==(nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 then
           nLLeg[iL,k] <= nLLegNz2_UB[ nNodePipe[iL] ]
         else
           nLLeg[iL,k] == 0
         endif
       else
                             %%% NOT HERE: nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] /\
         nLLeg[iL,k] <= nLLeg_UB[ nNodePipe[iL] ]
       endif
  endif );
%%% ACTUALLY CONSTRAIN LEG BOX ENDS AND CONNECT TO THE LENGTH
constraint forall( iL in TPIPELEGS, k in TCOORDS )(       %% ALWAYS ADD RADIUS, EVEN ON ENDS
    nXLeg1[iL,k] <= nXNd[iL,k]-nRadius[nNodePipe[iL]] /\ nXLeg1[iL,k] <= nXNd[iL+1,k]-nRadius[nNodePipe[iL]]
    /\                          %% >=: +nRadius
    nXLeg2[iL,k] >= nXNd[iL,k]+nRadius[nNodePipe[iL]] /\ nXLeg2[iL,k] >= nXNd[iL+1,k]+nRadius[nNodePipe[iL]]
    /\       %%% CONNECTING TO LENGTHS
    nLLeg[ iL,k] == nXLeg2[iL,k] - nXLeg1[iL,k] - 2*nRadius[nNodePipe[iL]]
  );
%%% Leg sequence
constraint forall( iP in TPIPES )(
  1==sum( iL in TPIPELEGS_BYPIPE[iP] )
       ( fLastLeg[iL] )                               %% Also constraint fExistLeg's?
  /\ 0==fLastLeg[ nPipeLeg1st[iP] ]                   %% Not the starting 2 legs
  /\ 0==fLastLeg[ nPipeLeg1st[iP]+1 ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP] ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP]+1 ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP]+2 ]
);
constraint forall( iL in TPIPELEGS )(
  if isLastPossLeg(iL) then
    fExistLeg[iL] == fLastLeg[iL]
  else
    fExistLeg[iL] == fExistLeg[iL+1]+fLastLeg[iL]
  endif
  /\
  ( fExistLeg[iL]>0 <-> nDirLeg[iL]>0 )
);
%%% CONNECT LENGTHS TO DIRECTIONS
constraint forall( iL in TPIPELEGS, k in TCOORDS )(
  ( k==nDirLeg[iL] -> ( nLLeg[iL,k] <= nXNd[iL+1,k]-nXNd[iL,k] ) )
  /\
%%  ( (k==nDirLeg[iL]) + (k+3==nDirLeg[iL]) <= ( nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] ) )
  ( nDirLeg[iL] in {k, k+3} -> ( nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] ) )
  /\
  ( k+3==nDirLeg[iL] -> ( nLLeg[iL,k] <= nXNd[iL,k]-nXNd[iL+1,k] ) )
  /\
%%  ( 0==nDirLeg[iL] -> ( nLLeg[iL,k] <= 0 ) )
  ( not (nDirLeg[iL] in {k,k+3}) -> ( nLLeg[iL,k] <= 0 ) )
);
%%% ORTHOGONALITY OF LEGS  ( => NOT GOING BACK )
constraint forall( iL in TPIPELEGS, k in TCOORDS where not isLastPossLeg(iL) )(
  (nDirLeg[iL]==k) + (nDirLeg[iL]==k+3) + (nDirLeg[iL+1]==k) + (nDirLeg[iL+1]==k+3) <= 1
);
%% Constraining end nozzle lengths
constraint forall( iL in TPIPELEGS, k in TCOORDS )(
  ( 1==fLastLeg[iL] -> ( nDirLeg[iL]==nDirNz2[ nNodePipe[iL] ] ) )
  /\
  ( 1==fLastLeg[iL] -> nLLeg[ iL, (nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 ] >= nLLegNz2_LB[ nNodePipe[iL] ] )
  /\
  ( 1==fLastLeg[iL] -> nLLeg[ iL, (nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 ] <= nLLegNz2_UB[ nNodePipe[iL] ] )
  /\
  ( 1==fLastLeg[iL] -> nXNd[ iL+1, k ] == nXNd[ nPipeLegLast[nNodePipe[iL]]+1, k ] )    %% Set to the nz2 connection
);       %%% TODO Could add more direct implications on the low-level vars

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (Non-strict) disjointness of OBSTACLE BOXES & LEGS along each coord axis,
%% regarding SAFETY DISTANCE
%% HOW to handle in & out of a module / support zone?
array[int, int, int] of var bool: bDisjLegBox_K = array3d( TBOXES, TPIPELEGS_RANGE, TCOORDS,
  [ if 2<nBoxType[iB] \/ not isActualLeg(iL) then true
    else
      nXBx2[iB,k] + nDSf2Pi[iB] <= nXLeg1[iL,k] \/ nXBx[iB,k] - nDSf2Pi[iB] >= nXLeg2[iL,k]
    endif
    | iB in TBOXES, iL in TPIPELEGS_RANGE, k in TCOORDS ]
);
constraint forall( iB in TBOXES, iL in TPIPELEGS where 2>=nBoxType[iB]
    /\ ( not isFirstLeg(iL) \/ iB!=nNz1ModuleBox[ nNodePipe[iL] ] ) )(        %% Avoid checking 1st leg X its box
  if iB!=nNz2ModuleBox[ nNodePipe[iL] ] then 
    exists( k in TCOORDS )( bDisjLegBox_K[iB,iL,k] )
  else
    exists( k in TCOORDS )( bDisjLegBox_K[iB,iL,k] )
    \/ 1==fLastLeg[iL] \/ 0==fExistLeg[iL]
  endif
);
%% Disjointness to other pipes' legs. TODO Need own legs??? BUT THEN over 2 legs.
array[int, int, int] of var bool: bLeftLegLeg_K = array3d( TPIPELEGS_RANGE, TPIPELEGS_RANGE, TCOORDS,
  [ if nNodePipe[i1]==nNodePipe[i2] \/ not isActualLeg(i1) \/ not isActualLeg(i2) \/ i1==i2 then true
    else
      nXLeg2[i1,k] + nDSf_Pi2Pi <= nXLeg1[i2,k]
    endif
    | i1 in TPIPELEGS_RANGE, i2 in TPIPELEGS_RANGE, k in TCOORDS] );
constraint forall( i1, i2 in TPIPELEGS where nNodePipe[i1]<nNodePipe[i2] )(
  exists( k in TCOORDS )( bLeftLegLeg_K[ i1, i2, k ] \/ bLeftLegLeg_K[ i2, i1, k ] )
  \/ 0==fExistLeg[i1] \/ 0==fExistLeg[i2]
);
%% BEING IN A SUPPORT ZONE: FOR EACH BEND'S _BOTTOM_
%% This is also registered for rack preferred levels
array[ int, int ] of var bool: bInSZ = array2d( TPIPENODES, TBOXES,
  [
    if nBoxType[iZ]<3 then false
%    elseif isFirstLeg(iN) then true
    else
      forall( k in TCOORDS )(
        if 3==k then                       %% BOTTOM IN THE ZONE
          nXNd[iN,k]-nRadius[nNodePipe[iN]] >= nXBx[iZ,k]
          /\
          nXNd[iN,k]-nRadius[nNodePipe[iN]] <= nXBx2[iZ,k]
%% SEEM 50% longer:          nXNd[iN,k] in (nXBx[iZ,k]+nRadius[nNodePipe[iN]])..(nXBx2[iZ,k]+nRadius[nNodePipe[iN]])
        else                               %% NODE CENTER IN THE ZONE
          nXNd[iN,k] >= nXBx[iZ,k]
          /\
          nXNd[iN,k] <= nXBx2[iZ,k]
%% SEEM 50% longer:          nXNd[iN,k] in nXBx[iZ,k]..nXBx2[iZ,k]
        endif
      )
    endif
  | iN in TPIPENODES, iZ in TBOXES ]
);
%%% ACTUALLY DEMAND FOR EACH NODE TO BE IN A SUPPORT ZONE
constraint forall( iN in TPIPELEGS where not isFirstLeg(iN) )(
  exists( iZ in TSUPPORTS )( bInSZ[ iN, iZ ] )
);
%%% Node being NOT IN ANY PREFERRED SUPPORT LEVEL
array[int] of var 0..1: fNodeNotInPref = [
  if isFirstLeg(iN) \/ not isActualLeg(iN) then 0
  else
    1 - sum( iZ in T_RACKPREFLEVELS )( bInSZ[ iN, iZ ] )
  endif
  | iN in TPIPENODES ];
%%% Node support cost
array[int] of var int: nNodeCstSp = [
  if isFirstLeg(iN) \/ not isActualLeg(iN) then 0
  else
    fExistLeg[iN] *                             %%% MULTIPLY
      ( fNodeNotInPref[ iN ] * (nCostSupport0 div nOBJCOEFDIVISOR + 1) +
        sum( iZ in T_RACKPREFLEVELS )(
             bInSZ[ iN, iZ ] * (nBoxCostSupport[ iZ ] div nOBJCOEFDIVISOR + 1) ) )
  endif
  | iN in TPIPENODES ];
%%% No leg between disjoint support zones of different modules
%%% constraint forall( iL in  ------------------------------
%%% If required, a pipe has to go thru a rack
%%% 13.12.16   NO THIS LOOKS STRANGE. Better forbid jumping between
%%% modules unless to/from rack (how?)
%constraint forall( iP in TPIPES where 1==fThruRack[iP] )(
%  exists( iNode in TPIPELEGS_BYPIPE[iP], iZ in T_RACKS /*where not isFirstLeg*/ )(
%    bInSZ[ iNode, iZ ]
%  )
%);
  
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%% FLEXIBILITY %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: nCoefReductionFactor = 1;                  %% !!!!!!!!!!!!!!!!!!11
%%% Length range for all dimensions
%set of int: sLenRange = 0..max( nLLeg_UB );
%constraint trace( "  sLenRange: \(sLenRange)\n" );
%%% The cubes of possible length values
%array[int] of int: nL3 = array1d( sLenRange, [ (l*l*l) div nCoefReductionFactor | l in sLenRange ] );
%%% Cubed length variables
%array[int, int] of var int: nLLeg3 = array2d( TPIPELEGS_RANGE, TCOORDS,
%  [ if dGCM_Cpp[nNodePipe[iL]]<=0.0 then 0 else nL3[ nLLeg[iL, k] ] endif      %% optional
%    | iL in TPIPELEGS_RANGE, k in TCOORDS
%] );
%%% Sums of cubed lengths for all other dimensions, for each pipe
array[int, int ] of var int: nSumLLeg3Orthog = array2d( TPIPES, TCOORDS,
  [  sum( iL in TPIPELEGS_BYPIPE[iP], k1 in TCOORDS diff {k} )(
    if dGCM_Cpp[ iP ]<=0.0 then 0 else 
      pow( nLLeg[iL, k1], 3 ) /*nLLeg3[iL, k1]*/ endif )
    | iP in TPIPES, k in TCOORDS ] );
constraint let {
   %%% The Kappas
   float: dKappaF = int2float(nLengthUnitMM) / 304.8;               %% feet in the length unit
   float: dKappaI = int2float(nLengthUnitMM) / 25.4;                %% inches in the length unit
} in forall( iP in TPIPES, k in TCOORDS )(
    if dGCM_Cpp[iP]<=0.0 then true
    else
      let {
        %%% Nozzle distance in this dim
        int: nDeltaNz = abs( fix(nXNd[ nPipeLeg1st[iP], k ]) - fix(nXNd[ nPipeLegLast[iP]+1, k ]) );
        %%% The constraint coef
        int: nCoefL = ceil( dGCM_Cpp[iP] * int2float(nDeltaNz) / dKappaF );
        %constraint trace ( "  GCM:  PIPE \(iP):  COORD \(k):  CoefL = \(nCoefL)\n" );
      } in forall( iL in TPIPELEGS_BYPIPE[iP], k1 in TCOORDS diff {k} )(
          ((nCoefL + nCoefReductionFactor - 1) div nCoefReductionFactor) * nLLeg[iL,k1] <= nSumLLeg3Orthog[ iP, k ]
        )
    endif
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% SOLVE + OBJECTIVE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
var 1..10000000: objective;              %% ????? Dividing the coefs by nOBJCOEFDIVISOR - needed for Chuffed.   Add +1 to avoid 0
constraint objective =
  sum( iL in TPIPELEGS )( (nCostPipePerLenUnit[ nNodePipe[iL] ] div nOBJCOEFDIVISOR + 1)
          * sum( k in TCOORDS )( nLLeg[iL,k] ) )
  + sum ( iL in TPIPELEGS where not isFirstLeg(iL) )( (nCostBend[ nNodePipe[iL] ] div nOBJCOEFDIVISOR + 1) * fExistLeg[iL] )
  + sum ( iL in TPIPELEGS where not isFirstLeg(iL) )( nNodeCstSp[iL] )
  ;

annotation ann5_relations_grpAll;
ann5_relations_grpAll = seq_search([
        int_search(
            [ [
                fExistLeg[ iL ],
                nDirLeg[ iL ]
              ][k]
              | iL in TPIPELEGS_RANGE, k in 1..2 ]
            ,
            input_order, indomain_split, complete
        )
        , int_search( array1d( nXNd ), input_order, indomain_split, complete )
        , int_search( array1d( nXLeg1 ), input_order, indomain_split, complete )
        , int_search( array1d( nXLeg2 ), input_order, indomain_split, complete )
        , int_search( array1d( nLLeg ), input_order, indomain_split, complete )
        , int_search( fLastLeg, input_order, indomain_split, complete )
    ])
;

 
solve
    :: ann5_relations_grpAll
  minimize
    objective
    ;

%%% Uncomment the output declaration to directly produce drawable data on the scaled sizes
%output [
%  "PARALLELEPIPEDS\n"
%]
%++ [
%  if k<=3 then "\(100*nPosXYZ[ m, k ]),\t"
%  elseif k<=6 then "\(100*nSzWLH[ m, k-3 ]),\t"
%  else "  \(m)\n" endif
%  | m in MODULES, k in 1..7 ]
%++ [ "  OBJ = \(objective)\n" ]
%;
