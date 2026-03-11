include "globals.mzn";
var 0..5: chooseint_239; %optimise.state.ChooseInt@ef

var 0..5: unnamed_242; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_242;
constraint unnamed_242 = [chooseint_239, 5][iunnamed_242];

var 0..5: chooseint_268; %optimise.state.ChooseInt@10c

var 0..5: unnamed_271; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_271;
constraint unnamed_271 = [chooseint_268, 5][iunnamed_271];

var 0..5: chooseint_297; %optimise.state.ChooseInt@129

var 0..5: unnamed_300; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_300;
constraint unnamed_300 = [chooseint_297, 5][iunnamed_300];

var 0..5: chooseint_326; %optimise.state.ChooseInt@146

var 0..5: unnamed_329; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_329;
constraint unnamed_329 = [chooseint_326, 5][iunnamed_329];

var 0..5: chooseint_355; %optimise.state.ChooseInt@163

var 0..5: unnamed_358; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_358;
constraint unnamed_358 = [chooseint_355, 5][iunnamed_358];

var 0..5: chooseint_384; %optimise.state.ChooseInt@180

var 0..5: unnamed_387; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_387;
constraint unnamed_387 = [chooseint_384, 5][iunnamed_387];

var 0..5: chooseint_413; %optimise.state.ChooseInt@19d

var 0..5: unnamed_416; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_416;
constraint unnamed_416 = [chooseint_413, 5][iunnamed_416];

var 0..5: chooseint_442; %optimise.state.ChooseInt@1ba

var 0..5: unnamed_445; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_445;
constraint unnamed_445 = [chooseint_442, 5][iunnamed_445];

var 0..5: chooseint_471; %optimise.state.ChooseInt@1d7

var 0..5: unnamed_474; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_474;
constraint unnamed_474 = [chooseint_471, 5][iunnamed_474];

var 0..5: chooseint_500; %optimise.state.ChooseInt@1f4

var 0..5: unnamed_503; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_503;
constraint unnamed_503 = [chooseint_500, 5][iunnamed_503];

var 0..5: chooseint_529; %optimise.state.ChooseInt@211

var 0..5: unnamed_532; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_532;
constraint unnamed_532 = [chooseint_529, 5][iunnamed_532];

var 0..5: chooseint_558; %optimise.state.ChooseInt@22e

var 0..5: unnamed_561; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_561;
constraint unnamed_561 = [chooseint_558, 5][iunnamed_561];

var 0..5: chooseint_587; %optimise.state.ChooseInt@24b

var 0..5: unnamed_590; %ref (Literal: 0 [0]).unnamed -14
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -14
var 1..1: iunnamed_590;
constraint unnamed_590 = [chooseint_587, 5][iunnamed_590];


var 0..5: i_2025; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2025;
constraint i_2025 = [unnamed_242, 5][ii_2025];

var 0..5: Add_2026 = i_2025;


var 0..5: total_2044; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2044;
constraint total_2044 = [Add_2026, 5][itotal_2044];

var 0..5: i_2045; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2045;
constraint i_2045 = [unnamed_271, 5][ii_2045];

var 0..10: Add_2046 = (total_2044 + i_2045);


var 0..10: total_2064; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2064;
constraint total_2064 = [Add_2046, 10][itotal_2064];

var 0..5: i_2065; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2065;
constraint i_2065 = [unnamed_300, 5][ii_2065];

var 0..15: Add_2066 = (total_2064 + i_2065);


var 0..15: total_2084; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2084;
constraint total_2084 = [Add_2066, 15][itotal_2084];

var 0..5: i_2085; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2085;
constraint i_2085 = [unnamed_329, 5][ii_2085];

var 0..20: Add_2086 = (total_2084 + i_2085);


var 0..20: total_2104; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2104;
constraint total_2104 = [Add_2086, 20][itotal_2104];

var 0..5: i_2105; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2105;
constraint i_2105 = [unnamed_358, 5][ii_2105];

var 0..25: Add_2106 = (total_2104 + i_2105);


var 0..25: total_2124; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2124;
constraint total_2124 = [Add_2106, 25][itotal_2124];

var 0..5: i_2125; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2125;
constraint i_2125 = [unnamed_387, 5][ii_2125];

var 0..30: Add_2126 = (total_2124 + i_2125);


var 0..30: total_2144; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2144;
constraint total_2144 = [Add_2126, 30][itotal_2144];

var 0..5: i_2145; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2145;
constraint i_2145 = [unnamed_416, 5][ii_2145];

var 0..35: Add_2146 = (total_2144 + i_2145);


var 0..35: total_2164; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2164;
constraint total_2164 = [Add_2146, 35][itotal_2164];

var 0..5: i_2165; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2165;
constraint i_2165 = [unnamed_445, 5][ii_2165];

var 0..40: Add_2166 = (total_2164 + i_2165);


var 0..40: total_2184; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2184;
constraint total_2184 = [Add_2166, 40][itotal_2184];

var 0..5: i_2185; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2185;
constraint i_2185 = [unnamed_474, 5][ii_2185];

var 0..45: Add_2186 = (total_2184 + i_2185);


var 0..45: total_2204; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2204;
constraint total_2204 = [Add_2186, 45][itotal_2204];

var 0..5: i_2205; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2205;
constraint i_2205 = [unnamed_503, 5][ii_2205];

var 0..50: Add_2206 = (total_2204 + i_2205);


var 0..50: total_2224; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2224;
constraint total_2224 = [Add_2206, 50][itotal_2224];

var 0..5: i_2225; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2225;
constraint i_2225 = [unnamed_532, 5][ii_2225];

var 0..55: Add_2226 = (total_2224 + i_2225);


var 0..55: total_2244; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2244;
constraint total_2244 = [Add_2226, 55][itotal_2244];

var 0..5: i_2245; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2245;
constraint i_2245 = [unnamed_561, 5][ii_2245];

var 0..60: Add_2246 = (total_2244 + i_2245);


var 0..60: total_2264; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2264;
constraint total_2264 = [Add_2246, 60][itotal_2264];

var 0..5: i_2265; %ref (Literal: 0 [0]).i -24
% doing constraints for lookup query: ref (Literal: 0 [0]).i -24
var 1..1: ii_2265;
constraint i_2265 = [unnamed_590, 5][ii_2265];

var 0..65: Add_2266 = (total_2264 + i_2265);

var 0..65: total_2270; %ref (Literal: 0 [0]).total -22
% doing constraints for lookup query: ref (Literal: 0 [0]).total -22
var 1..1: itotal_2270;
constraint total_2270 = [Add_2266, 65][itotal_2270];

var 0..65: obj_max; %ref (Literal: 0 [0]).ret_evaluate -15
var -ub(obj_max)..-lb(obj_max): objective = -1 * obj_max;
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_evaluate -15
var 1..1: iobjective;
constraint obj_max = [total_2270, 65][iobjective];

var 0..5: grouptotal_647; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_647;
constraint grouptotal_647 = [unnamed_242, 5][igrouptotal_647];


var 0..10: Add_658 = (grouptotal_647 + unnamed_271);

var 0..10: grouptotal_674; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_674;
constraint grouptotal_674 = [Add_658, 10][igrouptotal_674];


var 0..15: Add_685 = (grouptotal_674 + unnamed_300);

var 0..15: grouptotal_701; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_701;
constraint grouptotal_701 = [Add_685, 15][igrouptotal_701];


var 0..20: Add_712 = (grouptotal_701 + unnamed_329);

var 0..20: grouptotal_728; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_728;
constraint grouptotal_728 = [Add_712, 20][igrouptotal_728];


var 0..25: Add_739 = (grouptotal_728 + unnamed_358);

var 0..25: grouptotal_755; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_755;
constraint grouptotal_755 = [Add_739, 25][igrouptotal_755];


var 0..30: Add_766 = (grouptotal_755 + unnamed_387);

var 0..30: grouptotal_781; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_781;
constraint grouptotal_781 = [Add_766, 30][igrouptotal_781];

var bool: Greater_783 = (grouptotal_781 > 19);


var 0..5: grouptotal_818; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_818;
constraint grouptotal_818 = [unnamed_271, 5][igrouptotal_818];


var 0..10: Add_829 = (grouptotal_818 + unnamed_300);

var 0..10: grouptotal_845; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_845;
constraint grouptotal_845 = [Add_829, 10][igrouptotal_845];


var 0..15: Add_856 = (grouptotal_845 + unnamed_329);

var 0..15: grouptotal_872; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_872;
constraint grouptotal_872 = [Add_856, 15][igrouptotal_872];


var 0..20: Add_883 = (grouptotal_872 + unnamed_358);

var 0..20: grouptotal_899; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_899;
constraint grouptotal_899 = [Add_883, 20][igrouptotal_899];


var 0..25: Add_910 = (grouptotal_899 + unnamed_387);

var 0..25: grouptotal_926; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_926;
constraint grouptotal_926 = [Add_910, 25][igrouptotal_926];


var 0..30: Add_937 = (grouptotal_926 + unnamed_416);

var 0..30: grouptotal_952; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_952;
constraint grouptotal_952 = [Add_937, 30][igrouptotal_952];

var bool: Greater_954 = (grouptotal_952 > 19);


var 0..5: grouptotal_989; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_989;
constraint grouptotal_989 = [unnamed_300, 5][igrouptotal_989];


var 0..10: Add_1000 = (grouptotal_989 + unnamed_329);

var 0..10: grouptotal_1016; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1016;
constraint grouptotal_1016 = [Add_1000, 10][igrouptotal_1016];


var 0..15: Add_1027 = (grouptotal_1016 + unnamed_358);

var 0..15: grouptotal_1043; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1043;
constraint grouptotal_1043 = [Add_1027, 15][igrouptotal_1043];


var 0..20: Add_1054 = (grouptotal_1043 + unnamed_387);

var 0..20: grouptotal_1070; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1070;
constraint grouptotal_1070 = [Add_1054, 20][igrouptotal_1070];


var 0..25: Add_1081 = (grouptotal_1070 + unnamed_416);

var 0..25: grouptotal_1097; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1097;
constraint grouptotal_1097 = [Add_1081, 25][igrouptotal_1097];


var 0..30: Add_1108 = (grouptotal_1097 + unnamed_445);

var 0..30: grouptotal_1123; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1123;
constraint grouptotal_1123 = [Add_1108, 30][igrouptotal_1123];

var bool: Greater_1125 = (grouptotal_1123 > 19);


var 0..5: grouptotal_1160; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1160;
constraint grouptotal_1160 = [unnamed_329, 5][igrouptotal_1160];


var 0..10: Add_1171 = (grouptotal_1160 + unnamed_358);

var 0..10: grouptotal_1187; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1187;
constraint grouptotal_1187 = [Add_1171, 10][igrouptotal_1187];


var 0..15: Add_1198 = (grouptotal_1187 + unnamed_387);

var 0..15: grouptotal_1214; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1214;
constraint grouptotal_1214 = [Add_1198, 15][igrouptotal_1214];


var 0..20: Add_1225 = (grouptotal_1214 + unnamed_416);

var 0..20: grouptotal_1241; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1241;
constraint grouptotal_1241 = [Add_1225, 20][igrouptotal_1241];


var 0..25: Add_1252 = (grouptotal_1241 + unnamed_445);

var 0..25: grouptotal_1268; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1268;
constraint grouptotal_1268 = [Add_1252, 25][igrouptotal_1268];


var 0..30: Add_1279 = (grouptotal_1268 + unnamed_474);

var 0..30: grouptotal_1294; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1294;
constraint grouptotal_1294 = [Add_1279, 30][igrouptotal_1294];

var bool: Greater_1296 = (grouptotal_1294 > 19);


var 0..5: grouptotal_1331; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1331;
constraint grouptotal_1331 = [unnamed_358, 5][igrouptotal_1331];


var 0..10: Add_1342 = (grouptotal_1331 + unnamed_387);

var 0..10: grouptotal_1358; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1358;
constraint grouptotal_1358 = [Add_1342, 10][igrouptotal_1358];


var 0..15: Add_1369 = (grouptotal_1358 + unnamed_416);

var 0..15: grouptotal_1385; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1385;
constraint grouptotal_1385 = [Add_1369, 15][igrouptotal_1385];


var 0..20: Add_1396 = (grouptotal_1385 + unnamed_445);

var 0..20: grouptotal_1412; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1412;
constraint grouptotal_1412 = [Add_1396, 20][igrouptotal_1412];


var 0..25: Add_1423 = (grouptotal_1412 + unnamed_474);

var 0..25: grouptotal_1439; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1439;
constraint grouptotal_1439 = [Add_1423, 25][igrouptotal_1439];


var 0..30: Add_1450 = (grouptotal_1439 + unnamed_503);

var 0..30: grouptotal_1465; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1465;
constraint grouptotal_1465 = [Add_1450, 30][igrouptotal_1465];

var bool: Greater_1467 = (grouptotal_1465 > 19);


var 0..5: grouptotal_1502; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1502;
constraint grouptotal_1502 = [unnamed_387, 5][igrouptotal_1502];


var 0..10: Add_1513 = (grouptotal_1502 + unnamed_416);

var 0..10: grouptotal_1529; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1529;
constraint grouptotal_1529 = [Add_1513, 10][igrouptotal_1529];


var 0..15: Add_1540 = (grouptotal_1529 + unnamed_445);

var 0..15: grouptotal_1556; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1556;
constraint grouptotal_1556 = [Add_1540, 15][igrouptotal_1556];


var 0..20: Add_1567 = (grouptotal_1556 + unnamed_474);

var 0..20: grouptotal_1583; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1583;
constraint grouptotal_1583 = [Add_1567, 20][igrouptotal_1583];


var 0..25: Add_1594 = (grouptotal_1583 + unnamed_503);

var 0..25: grouptotal_1610; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1610;
constraint grouptotal_1610 = [Add_1594, 25][igrouptotal_1610];


var 0..30: Add_1621 = (grouptotal_1610 + unnamed_532);

var 0..30: grouptotal_1636; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1636;
constraint grouptotal_1636 = [Add_1621, 30][igrouptotal_1636];

var bool: Greater_1638 = (grouptotal_1636 > 19);


var 0..5: grouptotal_1673; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1673;
constraint grouptotal_1673 = [unnamed_416, 5][igrouptotal_1673];


var 0..10: Add_1684 = (grouptotal_1673 + unnamed_445);

var 0..10: grouptotal_1700; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1700;
constraint grouptotal_1700 = [Add_1684, 10][igrouptotal_1700];


var 0..15: Add_1711 = (grouptotal_1700 + unnamed_474);

var 0..15: grouptotal_1727; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1727;
constraint grouptotal_1727 = [Add_1711, 15][igrouptotal_1727];


var 0..20: Add_1738 = (grouptotal_1727 + unnamed_503);

var 0..20: grouptotal_1754; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1754;
constraint grouptotal_1754 = [Add_1738, 20][igrouptotal_1754];


var 0..25: Add_1765 = (grouptotal_1754 + unnamed_532);

var 0..25: grouptotal_1781; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1781;
constraint grouptotal_1781 = [Add_1765, 25][igrouptotal_1781];


var 0..30: Add_1792 = (grouptotal_1781 + unnamed_561);

var 0..30: grouptotal_1807; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1807;
constraint grouptotal_1807 = [Add_1792, 30][igrouptotal_1807];

var bool: Greater_1809 = (grouptotal_1807 > 19);


var 0..5: grouptotal_1844; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1844;
constraint grouptotal_1844 = [unnamed_445, 5][igrouptotal_1844];


var 0..10: Add_1855 = (grouptotal_1844 + unnamed_474);

var 0..10: grouptotal_1871; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1871;
constraint grouptotal_1871 = [Add_1855, 10][igrouptotal_1871];


var 0..15: Add_1882 = (grouptotal_1871 + unnamed_503);

var 0..15: grouptotal_1898; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1898;
constraint grouptotal_1898 = [Add_1882, 15][igrouptotal_1898];


var 0..20: Add_1909 = (grouptotal_1898 + unnamed_532);

var 0..20: grouptotal_1925; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1925;
constraint grouptotal_1925 = [Add_1909, 20][igrouptotal_1925];


var 0..25: Add_1936 = (grouptotal_1925 + unnamed_561);

var 0..25: grouptotal_1952; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1952;
constraint grouptotal_1952 = [Add_1936, 25][igrouptotal_1952];


var 0..30: Add_1963 = (grouptotal_1952 + unnamed_590);

var 0..30: grouptotal_1978; %ref (Literal: 0 [0]).grouptotal -19
% doing constraints for lookup query: ref (Literal: 0 [0]).grouptotal -19
var 1..1: igrouptotal_1978;
constraint grouptotal_1978 = [Add_1963, 30][igrouptotal_1978];

var bool: Greater_1980 = (grouptotal_1978 > 19);

array[1..9] of var 1..9: prev;

constraint prev[1] = 2;
constraint prev[2] in {2,6}; %optimise.state.EndCond@7bf
constraint prev[3] in {1,3}; %optimise.state.EndCond@312
constraint prev[4] in {4,9}; %optimise.state.EndCond@5be
constraint prev[5] in {3,5}; %optimise.state.EndCond@3bd
constraint prev[6] in {6,8}; %optimise.state.EndCond@714
constraint prev[7] in {5,7}; %optimise.state.EndCond@468
constraint prev[8] in {4,8}; %optimise.state.EndCond@669
constraint prev[9] in {7,9}; %optimise.state.EndCond@513
constraint alldifferent (prev);
constraint (prev[3] = 1) -> not Greater_783;
constraint (prev[5] = 3) -> not Greater_954;
constraint (prev[7] = 5) -> not Greater_1125;
constraint (prev[9] = 7) -> not Greater_1296;
constraint (prev[4] = 9) -> not Greater_1467;
constraint (prev[8] = 4) -> not Greater_1638;
constraint (prev[6] = 8) -> not Greater_1809;
constraint (prev[2] = 6) -> not Greater_1980;
solve :: seq_search([
		 int_search([chooseint_239, chooseint_268, chooseint_297, chooseint_326, chooseint_355, chooseint_384, chooseint_413, chooseint_442, chooseint_471, chooseint_500, chooseint_529, chooseint_558, chooseint_587],input_order,indomain_min,complete),
		int_search(prev, first_fail, indomain_min, complete),
		bool_search([Greater_783, Greater_954, Greater_1125, Greater_1296, Greater_1467, Greater_1638, Greater_1809, Greater_1980], input_order, indomain_max, complete),
		int_search([chooseint_239, unnamed_242, iunnamed_242, chooseint_268, unnamed_271, iunnamed_271, chooseint_297, unnamed_300, iunnamed_300, chooseint_326, unnamed_329, iunnamed_329, chooseint_355, unnamed_358, iunnamed_358, chooseint_384, unnamed_387, iunnamed_387, chooseint_413, unnamed_416, iunnamed_416, chooseint_442, unnamed_445, iunnamed_445, chooseint_471, unnamed_474, iunnamed_474, chooseint_500, unnamed_503, iunnamed_503, chooseint_529, unnamed_532, iunnamed_532, chooseint_558, unnamed_561, iunnamed_561, chooseint_587, unnamed_590, iunnamed_590, i_2025, ii_2025, Add_2026, total_2044, itotal_2044, i_2045, ii_2045, Add_2046, total_2064, itotal_2064, i_2065, ii_2065, Add_2066, total_2084, itotal_2084, i_2085, ii_2085, Add_2086, total_2104, itotal_2104, i_2105, ii_2105, Add_2106, total_2124, itotal_2124, i_2125, ii_2125, Add_2126, total_2144, itotal_2144, i_2145, ii_2145, Add_2146, total_2164, itotal_2164, i_2165, ii_2165, Add_2166, total_2184, itotal_2184, i_2185, ii_2185, Add_2186, total_2204, itotal_2204, i_2205, ii_2205, Add_2206, total_2224, itotal_2224, i_2225, ii_2225, Add_2226, total_2244, itotal_2244, i_2245, ii_2245, Add_2246, total_2264, itotal_2264, i_2265, ii_2265, Add_2266, total_2270, itotal_2270, obj_max, objective, iobjective, grouptotal_647, igrouptotal_647, Add_658, grouptotal_674, igrouptotal_674, Add_685, grouptotal_701, igrouptotal_701, Add_712, grouptotal_728, igrouptotal_728, Add_739, grouptotal_755, igrouptotal_755, Add_766, grouptotal_781, igrouptotal_781, grouptotal_818, igrouptotal_818, Add_829, grouptotal_845, igrouptotal_845, Add_856, grouptotal_872, igrouptotal_872, Add_883, grouptotal_899, igrouptotal_899, Add_910, grouptotal_926, igrouptotal_926, Add_937, grouptotal_952, igrouptotal_952, grouptotal_989, igrouptotal_989, Add_1000, grouptotal_1016, igrouptotal_1016, Add_1027, grouptotal_1043, igrouptotal_1043, Add_1054, grouptotal_1070, igrouptotal_1070, Add_1081, grouptotal_1097, igrouptotal_1097, Add_1108, grouptotal_1123, igrouptotal_1123, grouptotal_1160, igrouptotal_1160, Add_1171, grouptotal_1187, igrouptotal_1187, Add_1198, grouptotal_1214, igrouptotal_1214, Add_1225, grouptotal_1241, igrouptotal_1241, Add_1252, grouptotal_1268, igrouptotal_1268, Add_1279, grouptotal_1294, igrouptotal_1294, grouptotal_1331, igrouptotal_1331, Add_1342, grouptotal_1358, igrouptotal_1358, Add_1369, grouptotal_1385, igrouptotal_1385, Add_1396, grouptotal_1412, igrouptotal_1412, Add_1423, grouptotal_1439, igrouptotal_1439, Add_1450, grouptotal_1465, igrouptotal_1465, grouptotal_1502, igrouptotal_1502, Add_1513, grouptotal_1529, igrouptotal_1529, Add_1540, grouptotal_1556, igrouptotal_1556, Add_1567, grouptotal_1583, igrouptotal_1583, Add_1594, grouptotal_1610, igrouptotal_1610, Add_1621, grouptotal_1636, igrouptotal_1636, grouptotal_1673, igrouptotal_1673, Add_1684, grouptotal_1700, igrouptotal_1700, Add_1711, grouptotal_1727, igrouptotal_1727, Add_1738, grouptotal_1754, igrouptotal_1754, Add_1765, grouptotal_1781, igrouptotal_1781, Add_1792, grouptotal_1807, igrouptotal_1807, grouptotal_1844, igrouptotal_1844, Add_1855, grouptotal_1871, igrouptotal_1871, Add_1882, grouptotal_1898, igrouptotal_1898, Add_1909, grouptotal_1925, igrouptotal_1925, Add_1936, grouptotal_1952, igrouptotal_1952, Add_1963, grouptotal_1978, igrouptotal_1978], first_fail, indomain_min, complete),
	])
	minimize objective;

output [
	"prev = \(prev);\n",
	"constraint Greater_783 = \(Greater_783);\n",
	"constraint Greater_954 = \(Greater_954);\n",
	"constraint Greater_1125 = \(Greater_1125);\n",
	"constraint Greater_1296 = \(Greater_1296);\n",
	"constraint Greater_1467 = \(Greater_1467);\n",
	"constraint Greater_1638 = \(Greater_1638);\n",
	"constraint Greater_1809 = \(Greater_1809);\n",
	"constraint Greater_1980 = \(Greater_1980);\n",
	"chooseint_239 = \(chooseint_239);\n",
	"unnamed_242 = \(unnamed_242);\n",
	"iunnamed_242 = \(iunnamed_242);\n",
	"chooseint_268 = \(chooseint_268);\n",
	"unnamed_271 = \(unnamed_271);\n",
	"iunnamed_271 = \(iunnamed_271);\n",
	"chooseint_297 = \(chooseint_297);\n",
	"unnamed_300 = \(unnamed_300);\n",
	"iunnamed_300 = \(iunnamed_300);\n",
	"chooseint_326 = \(chooseint_326);\n",
	"unnamed_329 = \(unnamed_329);\n",
	"iunnamed_329 = \(iunnamed_329);\n",
	"chooseint_355 = \(chooseint_355);\n",
	"unnamed_358 = \(unnamed_358);\n",
	"iunnamed_358 = \(iunnamed_358);\n",
	"chooseint_384 = \(chooseint_384);\n",
	"unnamed_387 = \(unnamed_387);\n",
	"iunnamed_387 = \(iunnamed_387);\n",
	"chooseint_413 = \(chooseint_413);\n",
	"unnamed_416 = \(unnamed_416);\n",
	"iunnamed_416 = \(iunnamed_416);\n",
	"chooseint_442 = \(chooseint_442);\n",
	"unnamed_445 = \(unnamed_445);\n",
	"iunnamed_445 = \(iunnamed_445);\n",
	"chooseint_471 = \(chooseint_471);\n",
	"unnamed_474 = \(unnamed_474);\n",
	"iunnamed_474 = \(iunnamed_474);\n",
	"chooseint_500 = \(chooseint_500);\n",
	"unnamed_503 = \(unnamed_503);\n",
	"iunnamed_503 = \(iunnamed_503);\n",
	"chooseint_529 = \(chooseint_529);\n",
	"unnamed_532 = \(unnamed_532);\n",
	"iunnamed_532 = \(iunnamed_532);\n",
	"chooseint_558 = \(chooseint_558);\n",
	"unnamed_561 = \(unnamed_561);\n",
	"iunnamed_561 = \(iunnamed_561);\n",
	"chooseint_587 = \(chooseint_587);\n",
	"unnamed_590 = \(unnamed_590);\n",
	"iunnamed_590 = \(iunnamed_590);\n",
	"i_2025 = \(i_2025);\n",
	"ii_2025 = \(ii_2025);\n",
	"constraint Add_2026 = \(Add_2026);\n",
	"total_2044 = \(total_2044);\n",
	"itotal_2044 = \(itotal_2044);\n",
	"i_2045 = \(i_2045);\n",
	"ii_2045 = \(ii_2045);\n",
	"constraint Add_2046 = \(Add_2046);\n",
	"total_2064 = \(total_2064);\n",
	"itotal_2064 = \(itotal_2064);\n",
	"i_2065 = \(i_2065);\n",
	"ii_2065 = \(ii_2065);\n",
	"constraint Add_2066 = \(Add_2066);\n",
	"total_2084 = \(total_2084);\n",
	"itotal_2084 = \(itotal_2084);\n",
	"i_2085 = \(i_2085);\n",
	"ii_2085 = \(ii_2085);\n",
	"constraint Add_2086 = \(Add_2086);\n",
	"total_2104 = \(total_2104);\n",
	"itotal_2104 = \(itotal_2104);\n",
	"i_2105 = \(i_2105);\n",
	"ii_2105 = \(ii_2105);\n",
	"constraint Add_2106 = \(Add_2106);\n",
	"total_2124 = \(total_2124);\n",
	"itotal_2124 = \(itotal_2124);\n",
	"i_2125 = \(i_2125);\n",
	"ii_2125 = \(ii_2125);\n",
	"constraint Add_2126 = \(Add_2126);\n",
	"total_2144 = \(total_2144);\n",
	"itotal_2144 = \(itotal_2144);\n",
	"i_2145 = \(i_2145);\n",
	"ii_2145 = \(ii_2145);\n",
	"constraint Add_2146 = \(Add_2146);\n",
	"total_2164 = \(total_2164);\n",
	"itotal_2164 = \(itotal_2164);\n",
	"i_2165 = \(i_2165);\n",
	"ii_2165 = \(ii_2165);\n",
	"constraint Add_2166 = \(Add_2166);\n",
	"total_2184 = \(total_2184);\n",
	"itotal_2184 = \(itotal_2184);\n",
	"i_2185 = \(i_2185);\n",
	"ii_2185 = \(ii_2185);\n",
	"constraint Add_2186 = \(Add_2186);\n",
	"total_2204 = \(total_2204);\n",
	"itotal_2204 = \(itotal_2204);\n",
	"i_2205 = \(i_2205);\n",
	"ii_2205 = \(ii_2205);\n",
	"constraint Add_2206 = \(Add_2206);\n",
	"total_2224 = \(total_2224);\n",
	"itotal_2224 = \(itotal_2224);\n",
	"i_2225 = \(i_2225);\n",
	"ii_2225 = \(ii_2225);\n",
	"constraint Add_2226 = \(Add_2226);\n",
	"total_2244 = \(total_2244);\n",
	"itotal_2244 = \(itotal_2244);\n",
	"i_2245 = \(i_2245);\n",
	"ii_2245 = \(ii_2245);\n",
	"constraint Add_2246 = \(Add_2246);\n",
	"total_2264 = \(total_2264);\n",
	"itotal_2264 = \(itotal_2264);\n",
	"i_2265 = \(i_2265);\n",
	"ii_2265 = \(ii_2265);\n",
	"constraint Add_2266 = \(Add_2266);\n",
	"total_2270 = \(total_2270);\n",
	"itotal_2270 = \(itotal_2270);\n",
	"obj_max = \(obj_max);\n",
	"iobjective = \(iobjective);\n",
	"grouptotal_647 = \(grouptotal_647);\n",
	"igrouptotal_647 = \(igrouptotal_647);\n",
	"constraint Add_658 = \(Add_658);\n",
	"grouptotal_674 = \(grouptotal_674);\n",
	"igrouptotal_674 = \(igrouptotal_674);\n",
	"constraint Add_685 = \(Add_685);\n",
	"grouptotal_701 = \(grouptotal_701);\n",
	"igrouptotal_701 = \(igrouptotal_701);\n",
	"constraint Add_712 = \(Add_712);\n",
	"grouptotal_728 = \(grouptotal_728);\n",
	"igrouptotal_728 = \(igrouptotal_728);\n",
	"constraint Add_739 = \(Add_739);\n",
	"grouptotal_755 = \(grouptotal_755);\n",
	"igrouptotal_755 = \(igrouptotal_755);\n",
	"constraint Add_766 = \(Add_766);\n",
	"grouptotal_781 = \(grouptotal_781);\n",
	"igrouptotal_781 = \(igrouptotal_781);\n",
	"grouptotal_818 = \(grouptotal_818);\n",
	"igrouptotal_818 = \(igrouptotal_818);\n",
	"constraint Add_829 = \(Add_829);\n",
	"grouptotal_845 = \(grouptotal_845);\n",
	"igrouptotal_845 = \(igrouptotal_845);\n",
	"constraint Add_856 = \(Add_856);\n",
	"grouptotal_872 = \(grouptotal_872);\n",
	"igrouptotal_872 = \(igrouptotal_872);\n",
	"constraint Add_883 = \(Add_883);\n",
	"grouptotal_899 = \(grouptotal_899);\n",
	"igrouptotal_899 = \(igrouptotal_899);\n",
	"constraint Add_910 = \(Add_910);\n",
	"grouptotal_926 = \(grouptotal_926);\n",
	"igrouptotal_926 = \(igrouptotal_926);\n",
	"constraint Add_937 = \(Add_937);\n",
	"grouptotal_952 = \(grouptotal_952);\n",
	"igrouptotal_952 = \(igrouptotal_952);\n",
	"grouptotal_989 = \(grouptotal_989);\n",
	"igrouptotal_989 = \(igrouptotal_989);\n",
	"constraint Add_1000 = \(Add_1000);\n",
	"grouptotal_1016 = \(grouptotal_1016);\n",
	"igrouptotal_1016 = \(igrouptotal_1016);\n",
	"constraint Add_1027 = \(Add_1027);\n",
	"grouptotal_1043 = \(grouptotal_1043);\n",
	"igrouptotal_1043 = \(igrouptotal_1043);\n",
	"constraint Add_1054 = \(Add_1054);\n",
	"grouptotal_1070 = \(grouptotal_1070);\n",
	"igrouptotal_1070 = \(igrouptotal_1070);\n",
	"constraint Add_1081 = \(Add_1081);\n",
	"grouptotal_1097 = \(grouptotal_1097);\n",
	"igrouptotal_1097 = \(igrouptotal_1097);\n",
	"constraint Add_1108 = \(Add_1108);\n",
	"grouptotal_1123 = \(grouptotal_1123);\n",
	"igrouptotal_1123 = \(igrouptotal_1123);\n",
	"grouptotal_1160 = \(grouptotal_1160);\n",
	"igrouptotal_1160 = \(igrouptotal_1160);\n",
	"constraint Add_1171 = \(Add_1171);\n",
	"grouptotal_1187 = \(grouptotal_1187);\n",
	"igrouptotal_1187 = \(igrouptotal_1187);\n",
	"constraint Add_1198 = \(Add_1198);\n",
	"grouptotal_1214 = \(grouptotal_1214);\n",
	"igrouptotal_1214 = \(igrouptotal_1214);\n",
	"constraint Add_1225 = \(Add_1225);\n",
	"grouptotal_1241 = \(grouptotal_1241);\n",
	"igrouptotal_1241 = \(igrouptotal_1241);\n",
	"constraint Add_1252 = \(Add_1252);\n",
	"grouptotal_1268 = \(grouptotal_1268);\n",
	"igrouptotal_1268 = \(igrouptotal_1268);\n",
	"constraint Add_1279 = \(Add_1279);\n",
	"grouptotal_1294 = \(grouptotal_1294);\n",
	"igrouptotal_1294 = \(igrouptotal_1294);\n",
	"grouptotal_1331 = \(grouptotal_1331);\n",
	"igrouptotal_1331 = \(igrouptotal_1331);\n",
	"constraint Add_1342 = \(Add_1342);\n",
	"grouptotal_1358 = \(grouptotal_1358);\n",
	"igrouptotal_1358 = \(igrouptotal_1358);\n",
	"constraint Add_1369 = \(Add_1369);\n",
	"grouptotal_1385 = \(grouptotal_1385);\n",
	"igrouptotal_1385 = \(igrouptotal_1385);\n",
	"constraint Add_1396 = \(Add_1396);\n",
	"grouptotal_1412 = \(grouptotal_1412);\n",
	"igrouptotal_1412 = \(igrouptotal_1412);\n",
	"constraint Add_1423 = \(Add_1423);\n",
	"grouptotal_1439 = \(grouptotal_1439);\n",
	"igrouptotal_1439 = \(igrouptotal_1439);\n",
	"constraint Add_1450 = \(Add_1450);\n",
	"grouptotal_1465 = \(grouptotal_1465);\n",
	"igrouptotal_1465 = \(igrouptotal_1465);\n",
	"grouptotal_1502 = \(grouptotal_1502);\n",
	"igrouptotal_1502 = \(igrouptotal_1502);\n",
	"constraint Add_1513 = \(Add_1513);\n",
	"grouptotal_1529 = \(grouptotal_1529);\n",
	"igrouptotal_1529 = \(igrouptotal_1529);\n",
	"constraint Add_1540 = \(Add_1540);\n",
	"grouptotal_1556 = \(grouptotal_1556);\n",
	"igrouptotal_1556 = \(igrouptotal_1556);\n",
	"constraint Add_1567 = \(Add_1567);\n",
	"grouptotal_1583 = \(grouptotal_1583);\n",
	"igrouptotal_1583 = \(igrouptotal_1583);\n",
	"constraint Add_1594 = \(Add_1594);\n",
	"grouptotal_1610 = \(grouptotal_1610);\n",
	"igrouptotal_1610 = \(igrouptotal_1610);\n",
	"constraint Add_1621 = \(Add_1621);\n",
	"grouptotal_1636 = \(grouptotal_1636);\n",
	"igrouptotal_1636 = \(igrouptotal_1636);\n",
	"grouptotal_1673 = \(grouptotal_1673);\n",
	"igrouptotal_1673 = \(igrouptotal_1673);\n",
	"constraint Add_1684 = \(Add_1684);\n",
	"grouptotal_1700 = \(grouptotal_1700);\n",
	"igrouptotal_1700 = \(igrouptotal_1700);\n",
	"constraint Add_1711 = \(Add_1711);\n",
	"grouptotal_1727 = \(grouptotal_1727);\n",
	"igrouptotal_1727 = \(igrouptotal_1727);\n",
	"constraint Add_1738 = \(Add_1738);\n",
	"grouptotal_1754 = \(grouptotal_1754);\n",
	"igrouptotal_1754 = \(igrouptotal_1754);\n",
	"constraint Add_1765 = \(Add_1765);\n",
	"grouptotal_1781 = \(grouptotal_1781);\n",
	"igrouptotal_1781 = \(igrouptotal_1781);\n",
	"constraint Add_1792 = \(Add_1792);\n",
	"grouptotal_1807 = \(grouptotal_1807);\n",
	"igrouptotal_1807 = \(igrouptotal_1807);\n",
	"grouptotal_1844 = \(grouptotal_1844);\n",
	"igrouptotal_1844 = \(igrouptotal_1844);\n",
	"constraint Add_1855 = \(Add_1855);\n",
	"grouptotal_1871 = \(grouptotal_1871);\n",
	"igrouptotal_1871 = \(igrouptotal_1871);\n",
	"constraint Add_1882 = \(Add_1882);\n",
	"grouptotal_1898 = \(grouptotal_1898);\n",
	"igrouptotal_1898 = \(igrouptotal_1898);\n",
	"constraint Add_1909 = \(Add_1909);\n",
	"grouptotal_1925 = \(grouptotal_1925);\n",
	"igrouptotal_1925 = \(igrouptotal_1925);\n",
	"constraint Add_1936 = \(Add_1936);\n",
	"grouptotal_1952 = \(grouptotal_1952);\n",
	"igrouptotal_1952 = \(igrouptotal_1952);\n",
	"constraint Add_1963 = \(Add_1963);\n",
	"grouptotal_1978 = \(grouptotal_1978);\n",
	"igrouptotal_1978 = \(igrouptotal_1978);\n",
	"constraint objective = \(objective);\n",
];

