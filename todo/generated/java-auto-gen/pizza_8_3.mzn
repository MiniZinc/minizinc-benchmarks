include "globals.mzn";
var {23,29,35,41,47,53,65}: chooseobj_1530; %optimise.state.ChooseObject@5fa
constraint chooseobj_1530 in {23, 29, 35, 41, 47, 53, 65};

var {23,29,35,41,47,53,65}: pizza_1539; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_1539;
constraint pizza_1539 = [chooseobj_1530, 65][ipizza_1539];

var {23,29,35,41,47,53,65}: chooseobj_1581; %optimise.state.ChooseObject@62d
constraint chooseobj_1581 in {23, 29, 35, 41, 47, 53, 65};

var {23,29,35,41,47,53,65}: pizza_1590; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_1590;
constraint pizza_1590 = [chooseobj_1581, 65][ipizza_1590];

var 0..1: numSlices_1599; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..8: inumSlices_1599;
constraint [23, 29, 35, 41, 47, 53, 65, pizza_1539, pizza_1590][inumSlices_1599] = pizza_1590;
constraint ((pizza_1590 = 23)) -> inumSlices_1599 >= 1;
constraint ((pizza_1590 = 29)) -> inumSlices_1599 >= 2;
constraint ((pizza_1590 = 35)) -> inumSlices_1599 >= 3;
constraint ((pizza_1590 = 41)) -> inumSlices_1599 >= 4;
constraint ((pizza_1590 = 47)) -> inumSlices_1599 >= 5;
constraint ((pizza_1590 = 53)) -> inumSlices_1599 >= 6;
constraint ((pizza_1590 = 65)) -> inumSlices_1599 >= 7;
constraint ((pizza_1590 = pizza_1539)) -> inumSlices_1599 >= 8;
constraint numSlices_1599 = [0, 0, 0, 0, 0, 0, 0, 1, 1][inumSlices_1599];

var 1..2: Add_1601 = (numSlices_1599 + 1);

var {23,29,35,41,47,53,65}: chooseobj_1632; %optimise.state.ChooseObject@660
constraint chooseobj_1632 in {23, 29, 35, 41, 47, 53, 65};

var {23,29,35,41,47,53,65}: pizza_1641; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_1641;
constraint pizza_1641 = [chooseobj_1632, 65][ipizza_1641];

var 0..2: numSlices_1650; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..9: inumSlices_1650;
constraint [23, 29, 35, 41, 47, 53, 65, pizza_1539, pizza_1590, pizza_1641][inumSlices_1650] = pizza_1641;
constraint ((pizza_1641 = 23)) -> inumSlices_1650 >= 1;
constraint ((pizza_1641 = 29)) -> inumSlices_1650 >= 2;
constraint ((pizza_1641 = 35)) -> inumSlices_1650 >= 3;
constraint ((pizza_1641 = 41)) -> inumSlices_1650 >= 4;
constraint ((pizza_1641 = 47)) -> inumSlices_1650 >= 5;
constraint ((pizza_1641 = 53)) -> inumSlices_1650 >= 6;
constraint ((pizza_1641 = 65)) -> inumSlices_1650 >= 7;
constraint ((pizza_1641 = pizza_1539)) -> inumSlices_1650 >= 8;
constraint ((pizza_1641 = pizza_1590)) -> inumSlices_1650 >= 9;
constraint numSlices_1650 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, 2][inumSlices_1650];

var 1..3: Add_1652 = (numSlices_1650 + 1);

var {23,29,35,41,47,53,65}: chooseobj_1683; %optimise.state.ChooseObject@693
constraint chooseobj_1683 in {23, 29, 35, 41, 47, 53, 65};

var {23,29,35,41,47,53,65}: pizza_1692; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_1692;
constraint pizza_1692 = [chooseobj_1683, 65][ipizza_1692];

var 0..3: numSlices_1701; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..10: inumSlices_1701;
constraint [23, 29, 35, 41, 47, 53, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692][inumSlices_1701] = pizza_1692;
constraint ((pizza_1692 = 23)) -> inumSlices_1701 >= 1;
constraint ((pizza_1692 = 29)) -> inumSlices_1701 >= 2;
constraint ((pizza_1692 = 35)) -> inumSlices_1701 >= 3;
constraint ((pizza_1692 = 41)) -> inumSlices_1701 >= 4;
constraint ((pizza_1692 = 47)) -> inumSlices_1701 >= 5;
constraint ((pizza_1692 = 53)) -> inumSlices_1701 >= 6;
constraint ((pizza_1692 = 65)) -> inumSlices_1701 >= 7;
constraint ((pizza_1692 = pizza_1539)) -> inumSlices_1701 >= 8;
constraint ((pizza_1692 = pizza_1590)) -> inumSlices_1701 >= 9;
constraint ((pizza_1692 = pizza_1641)) -> inumSlices_1701 >= 10;
constraint numSlices_1701 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, Add_1652, 3][inumSlices_1701];

var 1..4: Add_1703 = (numSlices_1701 + 1);

var {23,29,35,41,47,53,65}: chooseobj_1734; %optimise.state.ChooseObject@6c6
constraint chooseobj_1734 in {23, 29, 35, 41, 47, 53, 65};

var {23,29,35,41,47,53,65}: pizza_1743; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_1743;
constraint pizza_1743 = [chooseobj_1734, 65][ipizza_1743];

var 0..4: numSlices_1752; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..11: inumSlices_1752;
constraint [23, 29, 35, 41, 47, 53, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743][inumSlices_1752] = pizza_1743;
constraint ((pizza_1743 = 23)) -> inumSlices_1752 >= 1;
constraint ((pizza_1743 = 29)) -> inumSlices_1752 >= 2;
constraint ((pizza_1743 = 35)) -> inumSlices_1752 >= 3;
constraint ((pizza_1743 = 41)) -> inumSlices_1752 >= 4;
constraint ((pizza_1743 = 47)) -> inumSlices_1752 >= 5;
constraint ((pizza_1743 = 53)) -> inumSlices_1752 >= 6;
constraint ((pizza_1743 = 65)) -> inumSlices_1752 >= 7;
constraint ((pizza_1743 = pizza_1539)) -> inumSlices_1752 >= 8;
constraint ((pizza_1743 = pizza_1590)) -> inumSlices_1752 >= 9;
constraint ((pizza_1743 = pizza_1641)) -> inumSlices_1752 >= 10;
constraint ((pizza_1743 = pizza_1692)) -> inumSlices_1752 >= 11;
constraint numSlices_1752 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, Add_1652, Add_1703, 4][inumSlices_1752];

var 1..5: Add_1754 = (numSlices_1752 + 1);

var {47,59,65}: chooseobj_2405; %optimise.state.ChooseObject@965
constraint chooseobj_2405 in {47, 59, 65};

var {47,59,65}: pizza_2414; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2414;
constraint pizza_2414 = [chooseobj_2405, 65][ipizza_2414];

var 0..5: numSlices_2423; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..8: inumSlices_2423;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414][inumSlices_2423] = pizza_2414;
constraint ((pizza_2414 = 47)) -> inumSlices_2423 >= 1;
constraint ((pizza_2414 = 59)) -> inumSlices_2423 >= 2;
constraint ((pizza_2414 = 65)) -> inumSlices_2423 >= 3;
constraint ((pizza_2414 = pizza_1539)) -> inumSlices_2423 >= 4;
constraint ((pizza_2414 = pizza_1590)) -> inumSlices_2423 >= 5;
constraint ((pizza_2414 = pizza_1641)) -> inumSlices_2423 >= 6;
constraint ((pizza_2414 = pizza_1692)) -> inumSlices_2423 >= 7;
constraint ((pizza_2414 = pizza_1743)) -> inumSlices_2423 >= 8;
constraint numSlices_2423 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, 5][inumSlices_2423];

var 1..6: Add_2425 = (numSlices_2423 + 1);

var {47,59,65}: chooseobj_2456; %optimise.state.ChooseObject@998
constraint chooseobj_2456 in {47, 59, 65};

var {47,59,65}: pizza_2465; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2465;
constraint pizza_2465 = [chooseobj_2456, 65][ipizza_2465];

var 0..6: numSlices_2474; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..9: inumSlices_2474;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465][inumSlices_2474] = pizza_2465;
constraint ((pizza_2465 = 47)) -> inumSlices_2474 >= 1;
constraint ((pizza_2465 = 59)) -> inumSlices_2474 >= 2;
constraint ((pizza_2465 = 65)) -> inumSlices_2474 >= 3;
constraint ((pizza_2465 = pizza_1539)) -> inumSlices_2474 >= 4;
constraint ((pizza_2465 = pizza_1590)) -> inumSlices_2474 >= 5;
constraint ((pizza_2465 = pizza_1641)) -> inumSlices_2474 >= 6;
constraint ((pizza_2465 = pizza_1692)) -> inumSlices_2474 >= 7;
constraint ((pizza_2465 = pizza_1743)) -> inumSlices_2474 >= 8;
constraint ((pizza_2465 = pizza_2414)) -> inumSlices_2474 >= 9;
constraint numSlices_2474 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, 6][inumSlices_2474];

var 1..7: Add_2476 = (numSlices_2474 + 1);

var {47,59,65}: chooseobj_2507; %optimise.state.ChooseObject@9cb
constraint chooseobj_2507 in {47, 59, 65};

var {47,59,65}: pizza_2516; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2516;
constraint pizza_2516 = [chooseobj_2507, 65][ipizza_2516];

var 0..7: numSlices_2525; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..10: inumSlices_2525;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516][inumSlices_2525] = pizza_2516;
constraint ((pizza_2516 = 47)) -> inumSlices_2525 >= 1;
constraint ((pizza_2516 = 59)) -> inumSlices_2525 >= 2;
constraint ((pizza_2516 = 65)) -> inumSlices_2525 >= 3;
constraint ((pizza_2516 = pizza_1539)) -> inumSlices_2525 >= 4;
constraint ((pizza_2516 = pizza_1590)) -> inumSlices_2525 >= 5;
constraint ((pizza_2516 = pizza_1641)) -> inumSlices_2525 >= 6;
constraint ((pizza_2516 = pizza_1692)) -> inumSlices_2525 >= 7;
constraint ((pizza_2516 = pizza_1743)) -> inumSlices_2525 >= 8;
constraint ((pizza_2516 = pizza_2414)) -> inumSlices_2525 >= 9;
constraint ((pizza_2516 = pizza_2465)) -> inumSlices_2525 >= 10;
constraint numSlices_2525 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, 7][inumSlices_2525];

var 1..8: Add_2527 = (numSlices_2525 + 1);

var {47,59,65}: chooseobj_2564; %optimise.state.ChooseObject@a04
constraint chooseobj_2564 in {47, 59, 65};

var {47,59,65}: pizza_2573; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2573;
constraint pizza_2573 = [chooseobj_2564, 65][ipizza_2573];

var 0..8: numSlices_2582; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..12: inumSlices_2582;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573][inumSlices_2582] = pizza_2573;
constraint [true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true][inumSlices_2582];
constraint ((pizza_2573 = 47)) -> inumSlices_2582 >= 1;
constraint ((pizza_2573 = 59)) -> inumSlices_2582 >= 2;
constraint ((pizza_2573 = 65)) -> inumSlices_2582 >= 3;
constraint ((pizza_2573 = pizza_1539)) -> inumSlices_2582 >= 4;
constraint ((pizza_2573 = pizza_1590)) -> inumSlices_2582 >= 5;
constraint ((pizza_2573 = pizza_1641)) -> inumSlices_2582 >= 6;
constraint ((pizza_2573 = pizza_1692)) -> inumSlices_2582 >= 7;
constraint ((pizza_2573 = pizza_1743)) -> inumSlices_2582 >= 8;
constraint ((pizza_2573 = pizza_2414)) -> inumSlices_2582 >= 9;
constraint ((pizza_2573 = pizza_2465)) -> inumSlices_2582 >= 10;
constraint ((pizza_2573 = pizza_2516)) -> inumSlices_2582 >= 11;
constraint ((equals_numSlices_2529__8 /\ (pizza_2573 = pizza_2516))) -> inumSlices_2582 >= 12;
constraint numSlices_2582 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, 8][inumSlices_2582];

var 1..9: Add_2584 = (numSlices_2582 + 1);

var 0..1: fullPizzas_2592; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..5: ifullPizzas_2592;
constraint [47, 59, 65, pizza_2516, pizza_2573][ifullPizzas_2592] = pizza_2573;
constraint [true, true, true, equals_numSlices_2529__8, true][ifullPizzas_2592];
constraint ((pizza_2573 = 47)) -> ifullPizzas_2592 >= 1;
constraint ((pizza_2573 = 59)) -> ifullPizzas_2592 >= 2;
constraint ((pizza_2573 = 65)) -> ifullPizzas_2592 >= 3;
constraint ((equals_numSlices_2529__8 /\ (pizza_2573 = pizza_2516))) -> ifullPizzas_2592 >= 4;
constraint fullPizzas_2592 = [0, 0, 0, 1, 1][ifullPizzas_2592];
constraint equals_numSlices_2586__8 -> (ifullPizzas_2592 < 5);
var 1..2: Add_2594 = (fullPizzas_2592 + 1);
var {47,59,65}: chooseobj_2621; %optimise.state.ChooseObject@a3d
constraint chooseobj_2621 in {47, 59, 65};

var {47,59,65}: pizza_2630; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2630;
constraint pizza_2630 = [chooseobj_2621, 65][ipizza_2630];

var 0..9: numSlices_2639; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..14: inumSlices_2639;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630][inumSlices_2639] = pizza_2630;
constraint [true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true][inumSlices_2639];
constraint ((pizza_2630 = 47)) -> inumSlices_2639 >= 1;
constraint ((pizza_2630 = 59)) -> inumSlices_2639 >= 2;
constraint ((pizza_2630 = 65)) -> inumSlices_2639 >= 3;
constraint ((pizza_2630 = pizza_1539)) -> inumSlices_2639 >= 4;
constraint ((pizza_2630 = pizza_1590)) -> inumSlices_2639 >= 5;
constraint ((pizza_2630 = pizza_1641)) -> inumSlices_2639 >= 6;
constraint ((pizza_2630 = pizza_1692)) -> inumSlices_2639 >= 7;
constraint ((pizza_2630 = pizza_1743)) -> inumSlices_2639 >= 8;
constraint ((pizza_2630 = pizza_2414)) -> inumSlices_2639 >= 9;
constraint ((pizza_2630 = pizza_2465)) -> inumSlices_2639 >= 10;
constraint ((pizza_2630 = pizza_2516)) -> inumSlices_2639 >= 11;
constraint ((equals_numSlices_2529__8 /\ (pizza_2630 = pizza_2516))) -> inumSlices_2639 >= 12;
constraint ((pizza_2630 = pizza_2573)) -> inumSlices_2639 >= 13;
constraint ((equals_numSlices_2586__8 /\ (pizza_2630 = pizza_2573))) -> inumSlices_2639 >= 14;
constraint numSlices_2639 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, 9][inumSlices_2639];

var 1..10: Add_2641 = (numSlices_2639 + 1);

var 0..2: fullPizzas_2649; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..6: ifullPizzas_2649;
constraint [47, 59, 65, pizza_2516, pizza_2573, pizza_2630][ifullPizzas_2649] = pizza_2630;
constraint [true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, true][ifullPizzas_2649];
constraint ((pizza_2630 = 47)) -> ifullPizzas_2649 >= 1;
constraint ((pizza_2630 = 59)) -> ifullPizzas_2649 >= 2;
constraint ((pizza_2630 = 65)) -> ifullPizzas_2649 >= 3;
constraint ((equals_numSlices_2529__8 /\ (pizza_2630 = pizza_2516))) -> ifullPizzas_2649 >= 4;
constraint ((equals_numSlices_2586__8 /\ (pizza_2630 = pizza_2573))) -> ifullPizzas_2649 >= 5;
constraint fullPizzas_2649 = [0, 0, 0, 1, Add_2594, 2][ifullPizzas_2649];
constraint equals_numSlices_2643__8 -> (ifullPizzas_2649 < 6);
var 1..3: Add_2651 = (fullPizzas_2649 + 1);
var {47,59,65}: chooseobj_2678; %optimise.state.ChooseObject@a76
constraint chooseobj_2678 in {47, 59, 65};

var {47,59,65}: pizza_2687; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2687;
constraint pizza_2687 = [chooseobj_2678, 65][ipizza_2687];

var 0..10: numSlices_2696; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..16: inumSlices_2696;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687][inumSlices_2696] = pizza_2687;
constraint [true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true][inumSlices_2696];
constraint ((pizza_2687 = 47)) -> inumSlices_2696 >= 1;
constraint ((pizza_2687 = 59)) -> inumSlices_2696 >= 2;
constraint ((pizza_2687 = 65)) -> inumSlices_2696 >= 3;
constraint ((pizza_2687 = pizza_1539)) -> inumSlices_2696 >= 4;
constraint ((pizza_2687 = pizza_1590)) -> inumSlices_2696 >= 5;
constraint ((pizza_2687 = pizza_1641)) -> inumSlices_2696 >= 6;
constraint ((pizza_2687 = pizza_1692)) -> inumSlices_2696 >= 7;
constraint ((pizza_2687 = pizza_1743)) -> inumSlices_2696 >= 8;
constraint ((pizza_2687 = pizza_2414)) -> inumSlices_2696 >= 9;
constraint ((pizza_2687 = pizza_2465)) -> inumSlices_2696 >= 10;
constraint ((pizza_2687 = pizza_2516)) -> inumSlices_2696 >= 11;
constraint ((equals_numSlices_2529__8 /\ (pizza_2687 = pizza_2516))) -> inumSlices_2696 >= 12;
constraint ((pizza_2687 = pizza_2573)) -> inumSlices_2696 >= 13;
constraint ((equals_numSlices_2586__8 /\ (pizza_2687 = pizza_2573))) -> inumSlices_2696 >= 14;
constraint ((pizza_2687 = pizza_2630)) -> inumSlices_2696 >= 15;
constraint ((equals_numSlices_2643__8 /\ (pizza_2687 = pizza_2630))) -> inumSlices_2696 >= 16;
constraint numSlices_2696 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, 10][inumSlices_2696];

var 1..11: Add_2698 = (numSlices_2696 + 1);

var 0..3: fullPizzas_2706; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..7: ifullPizzas_2706;
constraint [47, 59, 65, pizza_2516, pizza_2573, pizza_2630, pizza_2687][ifullPizzas_2706] = pizza_2687;
constraint [true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, true][ifullPizzas_2706];
constraint ((pizza_2687 = 47)) -> ifullPizzas_2706 >= 1;
constraint ((pizza_2687 = 59)) -> ifullPizzas_2706 >= 2;
constraint ((pizza_2687 = 65)) -> ifullPizzas_2706 >= 3;
constraint ((equals_numSlices_2529__8 /\ (pizza_2687 = pizza_2516))) -> ifullPizzas_2706 >= 4;
constraint ((equals_numSlices_2586__8 /\ (pizza_2687 = pizza_2573))) -> ifullPizzas_2706 >= 5;
constraint ((equals_numSlices_2643__8 /\ (pizza_2687 = pizza_2630))) -> ifullPizzas_2706 >= 6;
constraint fullPizzas_2706 = [0, 0, 0, 1, Add_2594, Add_2651, 3][ifullPizzas_2706];
constraint equals_numSlices_2700__8 -> (ifullPizzas_2706 < 7);
var 1..4: Add_2708 = (fullPizzas_2706 + 1);
var {47,59,65}: chooseobj_2735; %optimise.state.ChooseObject@aaf
constraint chooseobj_2735 in {47, 59, 65};

var {47,59,65}: pizza_2744; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_2744;
constraint pizza_2744 = [chooseobj_2735, 65][ipizza_2744];

var 0..11: numSlices_2753; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..18: inumSlices_2753;
constraint [47, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744][inumSlices_2753] = pizza_2744;
constraint [true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true][inumSlices_2753];
constraint ((pizza_2744 = 47)) -> inumSlices_2753 >= 1;
constraint ((pizza_2744 = 59)) -> inumSlices_2753 >= 2;
constraint ((pizza_2744 = 65)) -> inumSlices_2753 >= 3;
constraint ((pizza_2744 = pizza_1539)) -> inumSlices_2753 >= 4;
constraint ((pizza_2744 = pizza_1590)) -> inumSlices_2753 >= 5;
constraint ((pizza_2744 = pizza_1641)) -> inumSlices_2753 >= 6;
constraint ((pizza_2744 = pizza_1692)) -> inumSlices_2753 >= 7;
constraint ((pizza_2744 = pizza_1743)) -> inumSlices_2753 >= 8;
constraint ((pizza_2744 = pizza_2414)) -> inumSlices_2753 >= 9;
constraint ((pizza_2744 = pizza_2465)) -> inumSlices_2753 >= 10;
constraint ((pizza_2744 = pizza_2516)) -> inumSlices_2753 >= 11;
constraint ((equals_numSlices_2529__8 /\ (pizza_2744 = pizza_2516))) -> inumSlices_2753 >= 12;
constraint ((pizza_2744 = pizza_2573)) -> inumSlices_2753 >= 13;
constraint ((equals_numSlices_2586__8 /\ (pizza_2744 = pizza_2573))) -> inumSlices_2753 >= 14;
constraint ((pizza_2744 = pizza_2630)) -> inumSlices_2753 >= 15;
constraint ((equals_numSlices_2643__8 /\ (pizza_2744 = pizza_2630))) -> inumSlices_2753 >= 16;
constraint ((pizza_2744 = pizza_2687)) -> inumSlices_2753 >= 17;
constraint ((equals_numSlices_2700__8 /\ (pizza_2744 = pizza_2687))) -> inumSlices_2753 >= 18;
constraint numSlices_2753 = [0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, 11][inumSlices_2753];

var 1..12: Add_2755 = (numSlices_2753 + 1);

var 0..4: fullPizzas_2763; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..8: ifullPizzas_2763;
constraint [47, 59, 65, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744][ifullPizzas_2763] = pizza_2744;
constraint [true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, true][ifullPizzas_2763];
constraint ((pizza_2744 = 47)) -> ifullPizzas_2763 >= 1;
constraint ((pizza_2744 = 59)) -> ifullPizzas_2763 >= 2;
constraint ((pizza_2744 = 65)) -> ifullPizzas_2763 >= 3;
constraint ((equals_numSlices_2529__8 /\ (pizza_2744 = pizza_2516))) -> ifullPizzas_2763 >= 4;
constraint ((equals_numSlices_2586__8 /\ (pizza_2744 = pizza_2573))) -> ifullPizzas_2763 >= 5;
constraint ((equals_numSlices_2643__8 /\ (pizza_2744 = pizza_2630))) -> ifullPizzas_2763 >= 6;
constraint ((equals_numSlices_2700__8 /\ (pizza_2744 = pizza_2687))) -> ifullPizzas_2763 >= 7;
constraint fullPizzas_2763 = [0, 0, 0, 1, Add_2594, Add_2651, Add_2708, 4][ifullPizzas_2763];
constraint equals_numSlices_2757__8 -> (ifullPizzas_2763 < 8);
var 1..5: Add_2765 = (fullPizzas_2763 + 1);
var {29,35,41,47,53,59,65}: chooseobj_3496; %optimise.state.ChooseObject@da8
constraint chooseobj_3496 in {29, 35, 41, 47, 53, 59, 65};

var {29,35,41,47,53,59,65}: pizza_3505; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_3505;
constraint pizza_3505 = [chooseobj_3496, 65][ipizza_3505];

var 0..12: numSlices_3514; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..24: inumSlices_3514;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505][inumSlices_3514] = pizza_3505;
constraint [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true][inumSlices_3514];
constraint ((pizza_3505 = 29)) -> inumSlices_3514 >= 1;
constraint ((pizza_3505 = 35)) -> inumSlices_3514 >= 2;
constraint ((pizza_3505 = 41)) -> inumSlices_3514 >= 3;
constraint ((pizza_3505 = 47)) -> inumSlices_3514 >= 4;
constraint ((pizza_3505 = 53)) -> inumSlices_3514 >= 5;
constraint ((pizza_3505 = 59)) -> inumSlices_3514 >= 6;
constraint ((pizza_3505 = 65)) -> inumSlices_3514 >= 7;
constraint ((pizza_3505 = pizza_1539)) -> inumSlices_3514 >= 8;
constraint ((pizza_3505 = pizza_1590)) -> inumSlices_3514 >= 9;
constraint ((pizza_3505 = pizza_1641)) -> inumSlices_3514 >= 10;
constraint ((pizza_3505 = pizza_1692)) -> inumSlices_3514 >= 11;
constraint ((pizza_3505 = pizza_1743)) -> inumSlices_3514 >= 12;
constraint ((pizza_3505 = pizza_2414)) -> inumSlices_3514 >= 13;
constraint ((pizza_3505 = pizza_2465)) -> inumSlices_3514 >= 14;
constraint ((pizza_3505 = pizza_2516)) -> inumSlices_3514 >= 15;
constraint ((equals_numSlices_2529__8 /\ (pizza_3505 = pizza_2516))) -> inumSlices_3514 >= 16;
constraint ((pizza_3505 = pizza_2573)) -> inumSlices_3514 >= 17;
constraint ((equals_numSlices_2586__8 /\ (pizza_3505 = pizza_2573))) -> inumSlices_3514 >= 18;
constraint ((pizza_3505 = pizza_2630)) -> inumSlices_3514 >= 19;
constraint ((equals_numSlices_2643__8 /\ (pizza_3505 = pizza_2630))) -> inumSlices_3514 >= 20;
constraint ((pizza_3505 = pizza_2687)) -> inumSlices_3514 >= 21;
constraint ((equals_numSlices_2700__8 /\ (pizza_3505 = pizza_2687))) -> inumSlices_3514 >= 22;
constraint ((pizza_3505 = pizza_2744)) -> inumSlices_3514 >= 23;
constraint ((equals_numSlices_2757__8 /\ (pizza_3505 = pizza_2744))) -> inumSlices_3514 >= 24;
constraint numSlices_3514 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, 12][inumSlices_3514];

var 1..13: Add_3516 = (numSlices_3514 + 1);

var 0..5: fullPizzas_3524; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..13: ifullPizzas_3524;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505][ifullPizzas_3524] = pizza_3505;
constraint [true, true, true, true, true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, true][ifullPizzas_3524];
constraint ((pizza_3505 = 29)) -> ifullPizzas_3524 >= 1;
constraint ((pizza_3505 = 35)) -> ifullPizzas_3524 >= 2;
constraint ((pizza_3505 = 41)) -> ifullPizzas_3524 >= 3;
constraint ((pizza_3505 = 47)) -> ifullPizzas_3524 >= 4;
constraint ((pizza_3505 = 53)) -> ifullPizzas_3524 >= 5;
constraint ((pizza_3505 = 59)) -> ifullPizzas_3524 >= 6;
constraint ((pizza_3505 = 65)) -> ifullPizzas_3524 >= 7;
constraint ((equals_numSlices_2529__8 /\ (pizza_3505 = pizza_2516))) -> ifullPizzas_3524 >= 8;
constraint ((equals_numSlices_2586__8 /\ (pizza_3505 = pizza_2573))) -> ifullPizzas_3524 >= 9;
constraint ((equals_numSlices_2643__8 /\ (pizza_3505 = pizza_2630))) -> ifullPizzas_3524 >= 10;
constraint ((equals_numSlices_2700__8 /\ (pizza_3505 = pizza_2687))) -> ifullPizzas_3524 >= 11;
constraint ((equals_numSlices_2757__8 /\ (pizza_3505 = pizza_2744))) -> ifullPizzas_3524 >= 12;
constraint fullPizzas_3524 = [0, 0, 0, 0, 0, 0, 0, 1, Add_2594, Add_2651, Add_2708, Add_2765, 5][ifullPizzas_3524];
constraint equals_numSlices_3518__8 -> (ifullPizzas_3524 < 13);
var 1..6: Add_3526 = (fullPizzas_3524 + 1);
var {29,35,41,47,53,59,65}: chooseobj_3553; %optimise.state.ChooseObject@de1
constraint chooseobj_3553 in {29, 35, 41, 47, 53, 59, 65};

var {29,35,41,47,53,59,65}: pizza_3562; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_3562;
constraint pizza_3562 = [chooseobj_3553, 65][ipizza_3562];

var 0..13: numSlices_3571; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..26: inumSlices_3571;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562][inumSlices_3571] = pizza_3562;
constraint [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true][inumSlices_3571];
constraint ((pizza_3562 = 29)) -> inumSlices_3571 >= 1;
constraint ((pizza_3562 = 35)) -> inumSlices_3571 >= 2;
constraint ((pizza_3562 = 41)) -> inumSlices_3571 >= 3;
constraint ((pizza_3562 = 47)) -> inumSlices_3571 >= 4;
constraint ((pizza_3562 = 53)) -> inumSlices_3571 >= 5;
constraint ((pizza_3562 = 59)) -> inumSlices_3571 >= 6;
constraint ((pizza_3562 = 65)) -> inumSlices_3571 >= 7;
constraint ((pizza_3562 = pizza_1539)) -> inumSlices_3571 >= 8;
constraint ((pizza_3562 = pizza_1590)) -> inumSlices_3571 >= 9;
constraint ((pizza_3562 = pizza_1641)) -> inumSlices_3571 >= 10;
constraint ((pizza_3562 = pizza_1692)) -> inumSlices_3571 >= 11;
constraint ((pizza_3562 = pizza_1743)) -> inumSlices_3571 >= 12;
constraint ((pizza_3562 = pizza_2414)) -> inumSlices_3571 >= 13;
constraint ((pizza_3562 = pizza_2465)) -> inumSlices_3571 >= 14;
constraint ((pizza_3562 = pizza_2516)) -> inumSlices_3571 >= 15;
constraint ((equals_numSlices_2529__8 /\ (pizza_3562 = pizza_2516))) -> inumSlices_3571 >= 16;
constraint ((pizza_3562 = pizza_2573)) -> inumSlices_3571 >= 17;
constraint ((equals_numSlices_2586__8 /\ (pizza_3562 = pizza_2573))) -> inumSlices_3571 >= 18;
constraint ((pizza_3562 = pizza_2630)) -> inumSlices_3571 >= 19;
constraint ((equals_numSlices_2643__8 /\ (pizza_3562 = pizza_2630))) -> inumSlices_3571 >= 20;
constraint ((pizza_3562 = pizza_2687)) -> inumSlices_3571 >= 21;
constraint ((equals_numSlices_2700__8 /\ (pizza_3562 = pizza_2687))) -> inumSlices_3571 >= 22;
constraint ((pizza_3562 = pizza_2744)) -> inumSlices_3571 >= 23;
constraint ((equals_numSlices_2757__8 /\ (pizza_3562 = pizza_2744))) -> inumSlices_3571 >= 24;
constraint ((pizza_3562 = pizza_3505)) -> inumSlices_3571 >= 25;
constraint ((equals_numSlices_3518__8 /\ (pizza_3562 = pizza_3505))) -> inumSlices_3571 >= 26;
constraint numSlices_3571 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, 13][inumSlices_3571];

var 1..14: Add_3573 = (numSlices_3571 + 1);

var 0..6: fullPizzas_3581; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..14: ifullPizzas_3581;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505, pizza_3562][ifullPizzas_3581] = pizza_3562;
constraint [true, true, true, true, true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, true][ifullPizzas_3581];
constraint ((pizza_3562 = 29)) -> ifullPizzas_3581 >= 1;
constraint ((pizza_3562 = 35)) -> ifullPizzas_3581 >= 2;
constraint ((pizza_3562 = 41)) -> ifullPizzas_3581 >= 3;
constraint ((pizza_3562 = 47)) -> ifullPizzas_3581 >= 4;
constraint ((pizza_3562 = 53)) -> ifullPizzas_3581 >= 5;
constraint ((pizza_3562 = 59)) -> ifullPizzas_3581 >= 6;
constraint ((pizza_3562 = 65)) -> ifullPizzas_3581 >= 7;
constraint ((equals_numSlices_2529__8 /\ (pizza_3562 = pizza_2516))) -> ifullPizzas_3581 >= 8;
constraint ((equals_numSlices_2586__8 /\ (pizza_3562 = pizza_2573))) -> ifullPizzas_3581 >= 9;
constraint ((equals_numSlices_2643__8 /\ (pizza_3562 = pizza_2630))) -> ifullPizzas_3581 >= 10;
constraint ((equals_numSlices_2700__8 /\ (pizza_3562 = pizza_2687))) -> ifullPizzas_3581 >= 11;
constraint ((equals_numSlices_2757__8 /\ (pizza_3562 = pizza_2744))) -> ifullPizzas_3581 >= 12;
constraint ((equals_numSlices_3518__8 /\ (pizza_3562 = pizza_3505))) -> ifullPizzas_3581 >= 13;
constraint fullPizzas_3581 = [0, 0, 0, 0, 0, 0, 0, 1, Add_2594, Add_2651, Add_2708, Add_2765, Add_3526, 6][ifullPizzas_3581];
constraint equals_numSlices_3575__8 -> (ifullPizzas_3581 < 14);
var 1..7: Add_3583 = (fullPizzas_3581 + 1);
var {29,35,41,47,53,59,65}: chooseobj_3610; %optimise.state.ChooseObject@e1a
constraint chooseobj_3610 in {29, 35, 41, 47, 53, 59, 65};

var {29,35,41,47,53,59,65}: pizza_3619; %ref (Literal: 0 [0]).pizza -30
% doing constraints for lookup query: ref (Literal: 0 [0]).pizza -30
var 1..1: ipizza_3619;
constraint pizza_3619 = [chooseobj_3610, 65][ipizza_3619];

var 0..14: numSlices_3628; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..28: inumSlices_3628;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619][inumSlices_3628] = pizza_3619;
constraint [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true][inumSlices_3628];
constraint ((pizza_3619 = 29)) -> inumSlices_3628 >= 1;
constraint ((pizza_3619 = 35)) -> inumSlices_3628 >= 2;
constraint ((pizza_3619 = 41)) -> inumSlices_3628 >= 3;
constraint ((pizza_3619 = 47)) -> inumSlices_3628 >= 4;
constraint ((pizza_3619 = 53)) -> inumSlices_3628 >= 5;
constraint ((pizza_3619 = 59)) -> inumSlices_3628 >= 6;
constraint ((pizza_3619 = 65)) -> inumSlices_3628 >= 7;
constraint ((pizza_3619 = pizza_1539)) -> inumSlices_3628 >= 8;
constraint ((pizza_3619 = pizza_1590)) -> inumSlices_3628 >= 9;
constraint ((pizza_3619 = pizza_1641)) -> inumSlices_3628 >= 10;
constraint ((pizza_3619 = pizza_1692)) -> inumSlices_3628 >= 11;
constraint ((pizza_3619 = pizza_1743)) -> inumSlices_3628 >= 12;
constraint ((pizza_3619 = pizza_2414)) -> inumSlices_3628 >= 13;
constraint ((pizza_3619 = pizza_2465)) -> inumSlices_3628 >= 14;
constraint ((pizza_3619 = pizza_2516)) -> inumSlices_3628 >= 15;
constraint ((equals_numSlices_2529__8 /\ (pizza_3619 = pizza_2516))) -> inumSlices_3628 >= 16;
constraint ((pizza_3619 = pizza_2573)) -> inumSlices_3628 >= 17;
constraint ((equals_numSlices_2586__8 /\ (pizza_3619 = pizza_2573))) -> inumSlices_3628 >= 18;
constraint ((pizza_3619 = pizza_2630)) -> inumSlices_3628 >= 19;
constraint ((equals_numSlices_2643__8 /\ (pizza_3619 = pizza_2630))) -> inumSlices_3628 >= 20;
constraint ((pizza_3619 = pizza_2687)) -> inumSlices_3628 >= 21;
constraint ((equals_numSlices_2700__8 /\ (pizza_3619 = pizza_2687))) -> inumSlices_3628 >= 22;
constraint ((pizza_3619 = pizza_2744)) -> inumSlices_3628 >= 23;
constraint ((equals_numSlices_2757__8 /\ (pizza_3619 = pizza_2744))) -> inumSlices_3628 >= 24;
constraint ((pizza_3619 = pizza_3505)) -> inumSlices_3628 >= 25;
constraint ((equals_numSlices_3518__8 /\ (pizza_3619 = pizza_3505))) -> inumSlices_3628 >= 26;
constraint ((pizza_3619 = pizza_3562)) -> inumSlices_3628 >= 27;
constraint ((equals_numSlices_3575__8 /\ (pizza_3619 = pizza_3562))) -> inumSlices_3628 >= 28;
constraint numSlices_3628 = [0, 0, 0, 0, 0, 0, 0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, 14][inumSlices_3628];

var 1..15: Add_3630 = (numSlices_3628 + 1);

var 0..7: fullPizzas_3638; %ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.fullPizzas -10
var 1..15: ifullPizzas_3638;
constraint [29, 35, 41, 47, 53, 59, 65, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505, pizza_3562, pizza_3619][ifullPizzas_3638] = pizza_3619;
constraint [true, true, true, true, true, true, true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, equals_numSlices_3575__8, true][ifullPizzas_3638];
constraint ((pizza_3619 = 29)) -> ifullPizzas_3638 >= 1;
constraint ((pizza_3619 = 35)) -> ifullPizzas_3638 >= 2;
constraint ((pizza_3619 = 41)) -> ifullPizzas_3638 >= 3;
constraint ((pizza_3619 = 47)) -> ifullPizzas_3638 >= 4;
constraint ((pizza_3619 = 53)) -> ifullPizzas_3638 >= 5;
constraint ((pizza_3619 = 59)) -> ifullPizzas_3638 >= 6;
constraint ((pizza_3619 = 65)) -> ifullPizzas_3638 >= 7;
constraint ((equals_numSlices_2529__8 /\ (pizza_3619 = pizza_2516))) -> ifullPizzas_3638 >= 8;
constraint ((equals_numSlices_2586__8 /\ (pizza_3619 = pizza_2573))) -> ifullPizzas_3638 >= 9;
constraint ((equals_numSlices_2643__8 /\ (pizza_3619 = pizza_2630))) -> ifullPizzas_3638 >= 10;
constraint ((equals_numSlices_2700__8 /\ (pizza_3619 = pizza_2687))) -> ifullPizzas_3638 >= 11;
constraint ((equals_numSlices_2757__8 /\ (pizza_3619 = pizza_2744))) -> ifullPizzas_3638 >= 12;
constraint ((equals_numSlices_3518__8 /\ (pizza_3619 = pizza_3505))) -> ifullPizzas_3638 >= 13;
constraint ((equals_numSlices_3575__8 /\ (pizza_3619 = pizza_3562))) -> ifullPizzas_3638 >= 14;
constraint fullPizzas_3638 = [0, 0, 0, 0, 0, 0, 0, 1, Add_2594, Add_2651, Add_2708, Add_2765, Add_3526, Add_3583, 7][ifullPizzas_3638];
constraint equals_numSlices_3632__8 -> (ifullPizzas_3638 < 15);
var 1..8: Add_3640 = (fullPizzas_3638 + 1);
var 0..5: numSlices_3726; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..7: inumSlices_3726;
constraint [23, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, 23][inumSlices_3726] = 23;
constraint (true) -> inumSlices_3726 >= 1;
constraint ((23 = pizza_1539)) -> inumSlices_3726 >= 2;
constraint ((23 = pizza_1590)) -> inumSlices_3726 >= 3;
constraint ((23 = pizza_1641)) -> inumSlices_3726 >= 4;
constraint ((23 = pizza_1692)) -> inumSlices_3726 >= 5;
constraint ((23 = pizza_1743)) -> inumSlices_3726 >= 6;
constraint numSlices_3726 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, 5][inumSlices_3726];
constraint Greater_3724 -> (inumSlices_3726 < 7);
var {0,4,8,12,16,20}: Multiply_3728 = (numSlices_3726 * 4);
var {0,4,8,11,12,16,20}: slicesCost_3739; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_3739;
constraint [(not (Greater_3733 /\ Greater_3724)), (Greater_3733 /\ Greater_3724), true][islicesCost_3739];
constraint slicesCost_3739 = [Multiply_3728, 11, 20][islicesCost_3739];
constraint Greater_3724 -> (islicesCost_3739 < 3);
var {0,4,8,11,12,16,20}: Add_3740 = slicesCost_3739;
var {0,4,8,11,12,16,20}: cost_3743; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3743;
constraint [(not Greater_3724), Greater_3724, true][icost_3743];
constraint cost_3743 = [0, Add_3740, 20][icost_3743];

var {0,4,8,11,12,16,20}: ret_getCost_3747; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_3747;
constraint ret_getCost_3747 = [cost_3743, 20][iret_getCost_3747];

var {0,4,8,11,12,16,20}: Add_3748 = ret_getCost_3747;

var {0,4,8,11,12,16,20}: totalcost_3772; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_3772;
constraint totalcost_3772 = [Add_3748, 20][itotalcost_3772];

var 0..8: fullPizzas_3783; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..4: ifullPizzas_3783;
constraint [29, pizza_3505, pizza_3562, pizza_3619, 29][ifullPizzas_3783] = 29;
constraint [true, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_3783];
constraint (true) -> ifullPizzas_3783 >= 1;
constraint ((equals_numSlices_3518__8 /\ (29 = pizza_3505))) -> ifullPizzas_3783 >= 2;
constraint ((equals_numSlices_3575__8 /\ (29 = pizza_3562))) -> ifullPizzas_3783 >= 3;
constraint ((equals_numSlices_3632__8 /\ (29 = pizza_3619))) -> ifullPizzas_3783 >= 4;
constraint fullPizzas_3783 = [0, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_3783];

var {0,10,20,30,40,50,60,70,80}: Multiply_3785 = (fullPizzas_3783 * 10);

var 0..15: numSlices_3792; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..13: inumSlices_3792;
constraint [29, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 29][inumSlices_3792] = 29;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3792];
constraint (true) -> inumSlices_3792 >= 1;
constraint ((29 = pizza_1539)) -> inumSlices_3792 >= 2;
constraint ((29 = pizza_1590)) -> inumSlices_3792 >= 3;
constraint ((29 = pizza_1641)) -> inumSlices_3792 >= 4;
constraint ((29 = pizza_1692)) -> inumSlices_3792 >= 5;
constraint ((29 = pizza_1743)) -> inumSlices_3792 >= 6;
constraint ((29 = pizza_3505)) -> inumSlices_3792 >= 7;
constraint ((equals_numSlices_3518__8 /\ (29 = pizza_3505))) -> inumSlices_3792 >= 8;
constraint ((29 = pizza_3562)) -> inumSlices_3792 >= 9;
constraint ((equals_numSlices_3575__8 /\ (29 = pizza_3562))) -> inumSlices_3792 >= 10;
constraint ((29 = pizza_3619)) -> inumSlices_3792 >= 11;
constraint ((equals_numSlices_3632__8 /\ (29 = pizza_3619))) -> inumSlices_3792 >= 12;
constraint numSlices_3792 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3792];
constraint Greater_3790 -> (inumSlices_3792 < 13);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: Multiply_3794 = (numSlices_3792 * 5);
var {0,10,20,30,40,50,60,70,80}: cost_3804; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3804;
constraint cost_3804 = [Multiply_3785, 80][icost_3804];
constraint Greater_3790 -> (icost_3804 < 2);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_3805; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_3805;
constraint [(not (Greater_3799 /\ Greater_3790)), (Greater_3799 /\ Greater_3790), true][islicesCost_3805];
constraint slicesCost_3805 = [Multiply_3794, 10, 75][islicesCost_3805];
constraint Greater_3790 -> (islicesCost_3805 < 3);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100,105,110,115,120,125,130,135,140,145,150,155}: Add_3806 = (cost_3804 + slicesCost_3805);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100,105,110,115,120,125,130,135,140,145,150,155}: cost_3809; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3809;
constraint [(not Greater_3790), Greater_3790, true][icost_3809];
constraint cost_3809 = [Multiply_3785, Add_3806, 155][icost_3809];

var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100,105,110,115,120,125,130,135,140,145,150,155}: ret_getCost_3813; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_3813;
constraint ret_getCost_3813 = [cost_3809, 155][iret_getCost_3813];

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,165,166,167,170,171,175}: Add_3814 = (totalcost_3772 + ret_getCost_3813);

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,165,166,167,170,171,175}: totalcost_3838; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_3838;
constraint totalcost_3838 = [Add_3814, 175][itotalcost_3838];

var 0..8: fullPizzas_3849; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..4: ifullPizzas_3849;
constraint [35, pizza_3505, pizza_3562, pizza_3619, 35][ifullPizzas_3849] = 35;
constraint [true, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_3849];
constraint (true) -> ifullPizzas_3849 >= 1;
constraint ((equals_numSlices_3518__8 /\ (35 = pizza_3505))) -> ifullPizzas_3849 >= 2;
constraint ((equals_numSlices_3575__8 /\ (35 = pizza_3562))) -> ifullPizzas_3849 >= 3;
constraint ((equals_numSlices_3632__8 /\ (35 = pizza_3619))) -> ifullPizzas_3849 >= 4;
constraint fullPizzas_3849 = [0, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_3849];

var {0,14,28,42,56,70,84,98,112}: Multiply_3851 = (fullPizzas_3849 * 14);

var 0..15: numSlices_3858; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..13: inumSlices_3858;
constraint [35, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 35][inumSlices_3858] = 35;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3858];
constraint (true) -> inumSlices_3858 >= 1;
constraint ((35 = pizza_1539)) -> inumSlices_3858 >= 2;
constraint ((35 = pizza_1590)) -> inumSlices_3858 >= 3;
constraint ((35 = pizza_1641)) -> inumSlices_3858 >= 4;
constraint ((35 = pizza_1692)) -> inumSlices_3858 >= 5;
constraint ((35 = pizza_1743)) -> inumSlices_3858 >= 6;
constraint ((35 = pizza_3505)) -> inumSlices_3858 >= 7;
constraint ((equals_numSlices_3518__8 /\ (35 = pizza_3505))) -> inumSlices_3858 >= 8;
constraint ((35 = pizza_3562)) -> inumSlices_3858 >= 9;
constraint ((equals_numSlices_3575__8 /\ (35 = pizza_3562))) -> inumSlices_3858 >= 10;
constraint ((35 = pizza_3619)) -> inumSlices_3858 >= 11;
constraint ((equals_numSlices_3632__8 /\ (35 = pizza_3619))) -> inumSlices_3858 >= 12;
constraint numSlices_3858 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3858];
constraint Greater_3856 -> (inumSlices_3858 < 13);
var {0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60}: Multiply_3860 = (numSlices_3858 * 4);
var {0,14,28,42,56,70,84,98,112}: cost_3870; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3870;
constraint cost_3870 = [Multiply_3851, 112][icost_3870];
constraint Greater_3856 -> (icost_3870 < 2);
var {0,4,8,12,14,16,20,24,28,32,36,40,44,48,52,56,60}: slicesCost_3871; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_3871;
constraint [(not (Greater_3865 /\ Greater_3856)), (Greater_3865 /\ Greater_3856), true][islicesCost_3871];
constraint slicesCost_3871 = [Multiply_3860, 14, 60][islicesCost_3871];
constraint Greater_3856 -> (islicesCost_3871 < 3);
var {0,4,8,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,142,144,146,148,150,152,154,156,158,160,164,168,172}: Add_3872 = (cost_3870 + slicesCost_3871);
var {0,4,8,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,142,144,146,148,150,152,154,156,158,160,164,168,172}: cost_3875; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3875;
constraint [(not Greater_3856), Greater_3856, true][icost_3875];
constraint cost_3875 = [Multiply_3851, Add_3872, 172][icost_3875];

var {0,4,8,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,142,144,146,148,150,152,154,156,158,160,164,168,172}: ret_getCost_3879; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_3879;
constraint ret_getCost_3879 = [cost_3875, 172][iret_getCost_3879];

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,337,338,339,342,343,347}: Add_3880 = (totalcost_3838 + ret_getCost_3879);

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,337,338,339,342,343,347}: totalcost_3904; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_3904;
constraint totalcost_3904 = [Add_3880, 347][itotalcost_3904];

var 0..8: fullPizzas_3915; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..4: ifullPizzas_3915;
constraint [41, pizza_3505, pizza_3562, pizza_3619, 41][ifullPizzas_3915] = 41;
constraint [true, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_3915];
constraint (true) -> ifullPizzas_3915 >= 1;
constraint ((equals_numSlices_3518__8 /\ (41 = pizza_3505))) -> ifullPizzas_3915 >= 2;
constraint ((equals_numSlices_3575__8 /\ (41 = pizza_3562))) -> ifullPizzas_3915 >= 3;
constraint ((equals_numSlices_3632__8 /\ (41 = pizza_3619))) -> ifullPizzas_3915 >= 4;
constraint fullPizzas_3915 = [0, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_3915];

var {0,16,32,48,64,80,96,112,128}: Multiply_3917 = (fullPizzas_3915 * 16);

var 0..15: numSlices_3924; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..13: inumSlices_3924;
constraint [41, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 41][inumSlices_3924] = 41;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3924];
constraint (true) -> inumSlices_3924 >= 1;
constraint ((41 = pizza_1539)) -> inumSlices_3924 >= 2;
constraint ((41 = pizza_1590)) -> inumSlices_3924 >= 3;
constraint ((41 = pizza_1641)) -> inumSlices_3924 >= 4;
constraint ((41 = pizza_1692)) -> inumSlices_3924 >= 5;
constraint ((41 = pizza_1743)) -> inumSlices_3924 >= 6;
constraint ((41 = pizza_3505)) -> inumSlices_3924 >= 7;
constraint ((equals_numSlices_3518__8 /\ (41 = pizza_3505))) -> inumSlices_3924 >= 8;
constraint ((41 = pizza_3562)) -> inumSlices_3924 >= 9;
constraint ((equals_numSlices_3575__8 /\ (41 = pizza_3562))) -> inumSlices_3924 >= 10;
constraint ((41 = pizza_3619)) -> inumSlices_3924 >= 11;
constraint ((equals_numSlices_3632__8 /\ (41 = pizza_3619))) -> inumSlices_3924 >= 12;
constraint numSlices_3924 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3924];
constraint Greater_3922 -> (inumSlices_3924 < 13);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: Multiply_3926 = (numSlices_3924 * 5);
var {0,16,32,48,64,80,96,112,128}: cost_3936; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3936;
constraint cost_3936 = [Multiply_3917, 128][icost_3936];
constraint Greater_3922 -> (icost_3936 < 2);
var {0,5,10,15,16,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_3937; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_3937;
constraint [(not (Greater_3931 /\ Greater_3922)), (Greater_3931 /\ Greater_3922), true][islicesCost_3937];
constraint slicesCost_3937 = [Multiply_3926, 16, 75][islicesCost_3937];
constraint Greater_3922 -> (islicesCost_3937 < 3);
var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: Add_3938 = (cost_3936 + slicesCost_3937);
var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: cost_3941; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_3941;
constraint [(not Greater_3922), Greater_3922, true][icost_3941];
constraint cost_3941 = [Multiply_3917, Add_3938, 203][icost_3941];

var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: ret_getCost_3945; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_3945;
constraint ret_getCost_3945 = [cost_3941, 203][iret_getCost_3945];

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,540,541,542,545,546,550}: Add_3946 = (totalcost_3904 + ret_getCost_3945);

var {0,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,540,541,542,545,546,550}: totalcost_3970; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_3970;
constraint totalcost_3970 = [Add_3946, 550][itotalcost_3970];

var 0..8: fullPizzas_3981; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..9: ifullPizzas_3981;
constraint [47, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505, pizza_3562, pizza_3619, 47][ifullPizzas_3981] = 47;
constraint [true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_3981];
constraint (true) -> ifullPizzas_3981 >= 1;
constraint ((equals_numSlices_2529__8 /\ (47 = pizza_2516))) -> ifullPizzas_3981 >= 2;
constraint ((equals_numSlices_2586__8 /\ (47 = pizza_2573))) -> ifullPizzas_3981 >= 3;
constraint ((equals_numSlices_2643__8 /\ (47 = pizza_2630))) -> ifullPizzas_3981 >= 4;
constraint ((equals_numSlices_2700__8 /\ (47 = pizza_2687))) -> ifullPizzas_3981 >= 5;
constraint ((equals_numSlices_2757__8 /\ (47 = pizza_2744))) -> ifullPizzas_3981 >= 6;
constraint ((equals_numSlices_3518__8 /\ (47 = pizza_3505))) -> ifullPizzas_3981 >= 7;
constraint ((equals_numSlices_3575__8 /\ (47 = pizza_3562))) -> ifullPizzas_3981 >= 8;
constraint ((equals_numSlices_3632__8 /\ (47 = pizza_3619))) -> ifullPizzas_3981 >= 9;
constraint fullPizzas_3981 = [0, 1, Add_2594, Add_2651, Add_2708, Add_2765, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_3981];

var {0,10,20,30,40,50,60,70,80}: Multiply_3983 = (fullPizzas_3981 * 10);

var 0..15: numSlices_3990; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..25: inumSlices_3990;
constraint [47, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 47][inumSlices_3990] = 47;
constraint [true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3990];
constraint (true) -> inumSlices_3990 >= 1;
constraint ((47 = pizza_1539)) -> inumSlices_3990 >= 2;
constraint ((47 = pizza_1590)) -> inumSlices_3990 >= 3;
constraint ((47 = pizza_1641)) -> inumSlices_3990 >= 4;
constraint ((47 = pizza_1692)) -> inumSlices_3990 >= 5;
constraint ((47 = pizza_1743)) -> inumSlices_3990 >= 6;
constraint ((47 = pizza_2414)) -> inumSlices_3990 >= 7;
constraint ((47 = pizza_2465)) -> inumSlices_3990 >= 8;
constraint ((47 = pizza_2516)) -> inumSlices_3990 >= 9;
constraint ((equals_numSlices_2529__8 /\ (47 = pizza_2516))) -> inumSlices_3990 >= 10;
constraint ((47 = pizza_2573)) -> inumSlices_3990 >= 11;
constraint ((equals_numSlices_2586__8 /\ (47 = pizza_2573))) -> inumSlices_3990 >= 12;
constraint ((47 = pizza_2630)) -> inumSlices_3990 >= 13;
constraint ((equals_numSlices_2643__8 /\ (47 = pizza_2630))) -> inumSlices_3990 >= 14;
constraint ((47 = pizza_2687)) -> inumSlices_3990 >= 15;
constraint ((equals_numSlices_2700__8 /\ (47 = pizza_2687))) -> inumSlices_3990 >= 16;
constraint ((47 = pizza_2744)) -> inumSlices_3990 >= 17;
constraint ((equals_numSlices_2757__8 /\ (47 = pizza_2744))) -> inumSlices_3990 >= 18;
constraint ((47 = pizza_3505)) -> inumSlices_3990 >= 19;
constraint ((equals_numSlices_3518__8 /\ (47 = pizza_3505))) -> inumSlices_3990 >= 20;
constraint ((47 = pizza_3562)) -> inumSlices_3990 >= 21;
constraint ((equals_numSlices_3575__8 /\ (47 = pizza_3562))) -> inumSlices_3990 >= 22;
constraint ((47 = pizza_3619)) -> inumSlices_3990 >= 23;
constraint ((equals_numSlices_3632__8 /\ (47 = pizza_3619))) -> inumSlices_3990 >= 24;
constraint numSlices_3990 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3990];
constraint Greater_3988 -> (inumSlices_3990 < 25);
var {0,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45}: Multiply_3992 = (numSlices_3990 * 3);
var {0,10,20,30,40,50,60,70,80}: cost_4002; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4002;
constraint cost_4002 = [Multiply_3983, 80][icost_4002];
constraint Greater_3988 -> (icost_4002 < 2);
var {0,3,6,9,10,12,15,18,21,24,27,30,33,36,39,42,45}: slicesCost_4003; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_4003;
constraint [(not (Greater_3997 /\ Greater_3988)), (Greater_3997 /\ Greater_3988), true][islicesCost_4003];
constraint slicesCost_4003 = [Multiply_3992, 10, 45][islicesCost_4003];
constraint Greater_3988 -> (islicesCost_4003 < 3);
var {0,3,6,9,10,12,13,15,16,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,109,110,112,113,115,116,119,122,125}: Add_4004 = (cost_4002 + slicesCost_4003);
var {0,3,6,9,10,12,13,15,16,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,109,110,112,113,115,116,119,122,125}: cost_4007; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4007;
constraint [(not Greater_3988), Greater_3988, true][icost_4007];
constraint cost_4007 = [Multiply_3983, Add_4004, 125][icost_4007];

var {0,3,6,9,10,12,13,15,16,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,109,110,112,113,115,116,119,122,125}: ret_getCost_4011; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_4011;
constraint ret_getCost_4011 = [cost_4007, 125][iret_getCost_4011];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,675}: Add_4012 = (totalcost_3970 + ret_getCost_4011);

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,675}: totalcost_4036; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_4036;
constraint totalcost_4036 = [Add_4012, 675][itotalcost_4036];

var 0..8: fullPizzas_4047; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..4: ifullPizzas_4047;
constraint [53, pizza_3505, pizza_3562, pizza_3619, 53][ifullPizzas_4047] = 53;
constraint [true, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_4047];
constraint (true) -> ifullPizzas_4047 >= 1;
constraint ((equals_numSlices_3518__8 /\ (53 = pizza_3505))) -> ifullPizzas_4047 >= 2;
constraint ((equals_numSlices_3575__8 /\ (53 = pizza_3562))) -> ifullPizzas_4047 >= 3;
constraint ((equals_numSlices_3632__8 /\ (53 = pizza_3619))) -> ifullPizzas_4047 >= 4;
constraint fullPizzas_4047 = [0, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_4047];

var {0,15,30,45,60,75,90,105,120}: Multiply_4049 = (fullPizzas_4047 * 15);

var 0..15: numSlices_4056; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..13: inumSlices_4056;
constraint [53, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 53][inumSlices_4056] = 53;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4056];
constraint (true) -> inumSlices_4056 >= 1;
constraint ((53 = pizza_1539)) -> inumSlices_4056 >= 2;
constraint ((53 = pizza_1590)) -> inumSlices_4056 >= 3;
constraint ((53 = pizza_1641)) -> inumSlices_4056 >= 4;
constraint ((53 = pizza_1692)) -> inumSlices_4056 >= 5;
constraint ((53 = pizza_1743)) -> inumSlices_4056 >= 6;
constraint ((53 = pizza_3505)) -> inumSlices_4056 >= 7;
constraint ((equals_numSlices_3518__8 /\ (53 = pizza_3505))) -> inumSlices_4056 >= 8;
constraint ((53 = pizza_3562)) -> inumSlices_4056 >= 9;
constraint ((equals_numSlices_3575__8 /\ (53 = pizza_3562))) -> inumSlices_4056 >= 10;
constraint ((53 = pizza_3619)) -> inumSlices_4056 >= 11;
constraint ((equals_numSlices_3632__8 /\ (53 = pizza_3619))) -> inumSlices_4056 >= 12;
constraint numSlices_4056 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4056];
constraint Greater_4054 -> (inumSlices_4056 < 13);
var {0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60}: Multiply_4058 = (numSlices_4056 * 4);
var {0,15,30,45,60,75,90,105,120}: cost_4068; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4068;
constraint cost_4068 = [Multiply_4049, 120][icost_4068];
constraint Greater_4054 -> (icost_4068 < 2);
var {0,4,8,12,15,16,20,24,28,32,36,40,44,48,52,56,60}: slicesCost_4069; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_4069;
constraint [(not (Greater_4063 /\ Greater_4054)), (Greater_4063 /\ Greater_4054), true][islicesCost_4069];
constraint slicesCost_4069 = [Multiply_4058, 15, 60][islicesCost_4069];
constraint Greater_4054 -> (islicesCost_4069 < 3);
var {0,4,8,12,15,16,19,20,23,24,27,28,30,31,32,34,35,36,38,39,40,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,140,141,142,144,145,146,148,149,150,152,153,156,157,160,161,164,165,168,172,176,180}: Add_4070 = (cost_4068 + slicesCost_4069);
var {0,4,8,12,15,16,19,20,23,24,27,28,30,31,32,34,35,36,38,39,40,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,140,141,142,144,145,146,148,149,150,152,153,156,157,160,161,164,165,168,172,176,180}: cost_4073; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4073;
constraint [(not Greater_4054), Greater_4054, true][icost_4073];
constraint cost_4073 = [Multiply_4049, Add_4070, 180][icost_4073];

var {0,4,8,12,15,16,19,20,23,24,27,28,30,31,32,34,35,36,38,39,40,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,140,141,142,144,145,146,148,149,150,152,153,156,157,160,161,164,165,168,172,176,180}: ret_getCost_4077; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_4077;
constraint ret_getCost_4077 = [cost_4073, 180][iret_getCost_4077];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,855}: Add_4078 = (totalcost_4036 + ret_getCost_4077);

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,855}: totalcost_4102; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_4102;
constraint totalcost_4102 = [Add_4078, 855][itotalcost_4102];

var 0..8: fullPizzas_4113; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..9: ifullPizzas_4113;
constraint [59, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505, pizza_3562, pizza_3619, 59][ifullPizzas_4113] = 59;
constraint [true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_4113];
constraint (true) -> ifullPizzas_4113 >= 1;
constraint ((equals_numSlices_2529__8 /\ (59 = pizza_2516))) -> ifullPizzas_4113 >= 2;
constraint ((equals_numSlices_2586__8 /\ (59 = pizza_2573))) -> ifullPizzas_4113 >= 3;
constraint ((equals_numSlices_2643__8 /\ (59 = pizza_2630))) -> ifullPizzas_4113 >= 4;
constraint ((equals_numSlices_2700__8 /\ (59 = pizza_2687))) -> ifullPizzas_4113 >= 5;
constraint ((equals_numSlices_2757__8 /\ (59 = pizza_2744))) -> ifullPizzas_4113 >= 6;
constraint ((equals_numSlices_3518__8 /\ (59 = pizza_3505))) -> ifullPizzas_4113 >= 7;
constraint ((equals_numSlices_3575__8 /\ (59 = pizza_3562))) -> ifullPizzas_4113 >= 8;
constraint ((equals_numSlices_3632__8 /\ (59 = pizza_3619))) -> ifullPizzas_4113 >= 9;
constraint fullPizzas_4113 = [0, 1, Add_2594, Add_2651, Add_2708, Add_2765, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_4113];

var {0,11,22,33,44,55,66,77,88}: Multiply_4115 = (fullPizzas_4113 * 11);

var 0..15: numSlices_4122; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..20: inumSlices_4122;
constraint [59, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 59][inumSlices_4122] = 59;
constraint [true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4122];
constraint (true) -> inumSlices_4122 >= 1;
constraint ((59 = pizza_2414)) -> inumSlices_4122 >= 2;
constraint ((59 = pizza_2465)) -> inumSlices_4122 >= 3;
constraint ((59 = pizza_2516)) -> inumSlices_4122 >= 4;
constraint ((equals_numSlices_2529__8 /\ (59 = pizza_2516))) -> inumSlices_4122 >= 5;
constraint ((59 = pizza_2573)) -> inumSlices_4122 >= 6;
constraint ((equals_numSlices_2586__8 /\ (59 = pizza_2573))) -> inumSlices_4122 >= 7;
constraint ((59 = pizza_2630)) -> inumSlices_4122 >= 8;
constraint ((equals_numSlices_2643__8 /\ (59 = pizza_2630))) -> inumSlices_4122 >= 9;
constraint ((59 = pizza_2687)) -> inumSlices_4122 >= 10;
constraint ((equals_numSlices_2700__8 /\ (59 = pizza_2687))) -> inumSlices_4122 >= 11;
constraint ((59 = pizza_2744)) -> inumSlices_4122 >= 12;
constraint ((equals_numSlices_2757__8 /\ (59 = pizza_2744))) -> inumSlices_4122 >= 13;
constraint ((59 = pizza_3505)) -> inumSlices_4122 >= 14;
constraint ((equals_numSlices_3518__8 /\ (59 = pizza_3505))) -> inumSlices_4122 >= 15;
constraint ((59 = pizza_3562)) -> inumSlices_4122 >= 16;
constraint ((equals_numSlices_3575__8 /\ (59 = pizza_3562))) -> inumSlices_4122 >= 17;
constraint ((59 = pizza_3619)) -> inumSlices_4122 >= 18;
constraint ((equals_numSlices_3632__8 /\ (59 = pizza_3619))) -> inumSlices_4122 >= 19;
constraint numSlices_4122 = [0, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4122];
constraint Greater_4120 -> (inumSlices_4122 < 20);
var {0,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45}: Multiply_4124 = (numSlices_4122 * 3);
var {0,11,22,33,44,55,66,77,88}: cost_4134; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4134;
constraint cost_4134 = [Multiply_4115, 88][icost_4134];
constraint Greater_4120 -> (icost_4134 < 2);
var {0,3,6,9,11,12,15,18,21,24,27,30,33,36,39,42,45}: slicesCost_4135; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_4135;
constraint [(not (Greater_4129 /\ Greater_4120)), (Greater_4129 /\ Greater_4120), true][islicesCost_4135];
constraint slicesCost_4135 = [Multiply_4124, 11, 45][islicesCost_4135];
constraint Greater_4120 -> (islicesCost_4135 < 3);
var {0,3,6,9,11,12,14,15,17,18,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,115,116,118,119,121,122,124,127,130,133}: Add_4136 = (cost_4134 + slicesCost_4135);
var {0,3,6,9,11,12,14,15,17,18,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,115,116,118,119,121,122,124,127,130,133}: cost_4139; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4139;
constraint [(not Greater_4120), Greater_4120, true][icost_4139];
constraint cost_4139 = [Multiply_4115, Add_4136, 133][icost_4139];

var {0,3,6,9,11,12,14,15,17,18,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,115,116,118,119,121,122,124,127,130,133}: ret_getCost_4143; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_4143;
constraint ret_getCost_4143 = [cost_4139, 133][iret_getCost_4143];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,988}: Add_4144 = (totalcost_4102 + ret_getCost_4143);

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,988}: totalcost_4168; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_4168;
constraint totalcost_4168 = [Add_4144, 988][itotalcost_4168];

var 0..8: fullPizzas_4179; %ref ref (Literal: 0 [0]).item -35.fullPizzas -10
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.fullPizzas -10
var 1..9: ifullPizzas_4179;
constraint [65, pizza_2516, pizza_2573, pizza_2630, pizza_2687, pizza_2744, pizza_3505, pizza_3562, pizza_3619, 65][ifullPizzas_4179] = 65;
constraint [true, equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, true][ifullPizzas_4179];
constraint (true) -> ifullPizzas_4179 >= 1;
constraint ((equals_numSlices_2529__8 /\ (65 = pizza_2516))) -> ifullPizzas_4179 >= 2;
constraint ((equals_numSlices_2586__8 /\ (65 = pizza_2573))) -> ifullPizzas_4179 >= 3;
constraint ((equals_numSlices_2643__8 /\ (65 = pizza_2630))) -> ifullPizzas_4179 >= 4;
constraint ((equals_numSlices_2700__8 /\ (65 = pizza_2687))) -> ifullPizzas_4179 >= 5;
constraint ((equals_numSlices_2757__8 /\ (65 = pizza_2744))) -> ifullPizzas_4179 >= 6;
constraint ((equals_numSlices_3518__8 /\ (65 = pizza_3505))) -> ifullPizzas_4179 >= 7;
constraint ((equals_numSlices_3575__8 /\ (65 = pizza_3562))) -> ifullPizzas_4179 >= 8;
constraint ((equals_numSlices_3632__8 /\ (65 = pizza_3619))) -> ifullPizzas_4179 >= 9;
constraint fullPizzas_4179 = [0, 1, Add_2594, Add_2651, Add_2708, Add_2765, Add_3526, Add_3583, Add_3640, 8][ifullPizzas_4179];

var {0,16,32,48,64,80,96,112,128}: Multiply_4181 = (fullPizzas_4179 * 16);

var 0..15: numSlices_4188; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..25: inumSlices_4188;
constraint [65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 65][inumSlices_4188] = 65;
constraint [true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4188];
constraint (true) -> inumSlices_4188 >= 1;
constraint ((65 = pizza_1539)) -> inumSlices_4188 >= 2;
constraint ((65 = pizza_1590)) -> inumSlices_4188 >= 3;
constraint ((65 = pizza_1641)) -> inumSlices_4188 >= 4;
constraint ((65 = pizza_1692)) -> inumSlices_4188 >= 5;
constraint ((65 = pizza_1743)) -> inumSlices_4188 >= 6;
constraint ((65 = pizza_2414)) -> inumSlices_4188 >= 7;
constraint ((65 = pizza_2465)) -> inumSlices_4188 >= 8;
constraint ((65 = pizza_2516)) -> inumSlices_4188 >= 9;
constraint ((equals_numSlices_2529__8 /\ (65 = pizza_2516))) -> inumSlices_4188 >= 10;
constraint ((65 = pizza_2573)) -> inumSlices_4188 >= 11;
constraint ((equals_numSlices_2586__8 /\ (65 = pizza_2573))) -> inumSlices_4188 >= 12;
constraint ((65 = pizza_2630)) -> inumSlices_4188 >= 13;
constraint ((equals_numSlices_2643__8 /\ (65 = pizza_2630))) -> inumSlices_4188 >= 14;
constraint ((65 = pizza_2687)) -> inumSlices_4188 >= 15;
constraint ((equals_numSlices_2700__8 /\ (65 = pizza_2687))) -> inumSlices_4188 >= 16;
constraint ((65 = pizza_2744)) -> inumSlices_4188 >= 17;
constraint ((equals_numSlices_2757__8 /\ (65 = pizza_2744))) -> inumSlices_4188 >= 18;
constraint ((65 = pizza_3505)) -> inumSlices_4188 >= 19;
constraint ((equals_numSlices_3518__8 /\ (65 = pizza_3505))) -> inumSlices_4188 >= 20;
constraint ((65 = pizza_3562)) -> inumSlices_4188 >= 21;
constraint ((equals_numSlices_3575__8 /\ (65 = pizza_3562))) -> inumSlices_4188 >= 22;
constraint ((65 = pizza_3619)) -> inumSlices_4188 >= 23;
constraint ((equals_numSlices_3632__8 /\ (65 = pizza_3619))) -> inumSlices_4188 >= 24;
constraint numSlices_4188 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4188];
constraint Greater_4186 -> (inumSlices_4188 < 25);
var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: Multiply_4190 = (numSlices_4188 * 5);
var {0,16,32,48,64,80,96,112,128}: cost_4200; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4200;
constraint cost_4200 = [Multiply_4181, 128][icost_4200];
constraint Greater_4186 -> (icost_4200 < 2);
var {0,5,10,15,16,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_4201; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..3: islicesCost_4201;
constraint [(not (Greater_4195 /\ Greater_4186)), (Greater_4195 /\ Greater_4186), true][islicesCost_4201];
constraint slicesCost_4201 = [Multiply_4190, 16, 75][islicesCost_4201];
constraint Greater_4186 -> (islicesCost_4201 < 3);
var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: Add_4202 = (cost_4200 + slicesCost_4201);
var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: cost_4205; %ref (Literal: 0 [0]).cost -37
% doing constraints for lookup query: ref (Literal: 0 [0]).cost -37
var 1..2: icost_4205;
constraint [(not Greater_4186), Greater_4186, true][icost_4205];
constraint cost_4205 = [Multiply_4181, Add_4202, 203][icost_4205];

var {0,5,10,15,16,20,21,25,26,30,31,32,35,36,37,40,41,42,45,46,47,48,50,51,52,53,55,56,57,58,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,150,151,152,153,155,156,157,158,161,162,163,166,167,168,171,172,173,177,178,182,183,187,188,193,198,203}: ret_getCost_4209; %ref (Literal: 0 [0]).ret_getCost -36
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getCost -36
var 1..1: iret_getCost_4209;
constraint ret_getCost_4209 = [cost_4205, 203][iret_getCost_4209];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1191}: Add_4210 = (totalcost_4168 + ret_getCost_4209);

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1191}: totalcost_4214; %ref (Literal: 0 [0]).totalcost -33
% doing constraints for lookup query: ref (Literal: 0 [0]).totalcost -33
var 1..1: itotalcost_4214;
constraint totalcost_4214 = [Add_4210, 1191][itotalcost_4214];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1191}: ret_totalCost_4218; %ref (Literal: 0 [0]).ret_totalCost -32
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_totalCost -32
var 1..1: iret_totalCost_4218;
constraint ret_totalCost_4218 = [totalcost_4214, 1191][iret_totalCost_4218];

var {0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1191}: objective; %ref (Literal: 0 [0]).ret_evaluate -31
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_evaluate -31
var 1..1: iobjective;
constraint objective = [ret_totalCost_4218, 1191][iobjective];
var 1..8: numSlices_2529; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_2529;
constraint numSlices_2529 = [Add_2527, 8][inumSlices_2529];

var bool: equals_numSlices_2529__8 = (numSlices_2529 = 8);

var 1..9: numSlices_2586; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_2586;
constraint numSlices_2586 = [Add_2584, 9][inumSlices_2586];

var bool: equals_numSlices_2586__8 = (numSlices_2586 = 8);

var 1..10: numSlices_2643; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_2643;
constraint numSlices_2643 = [Add_2641, 10][inumSlices_2643];

var bool: equals_numSlices_2643__8 = (numSlices_2643 = 8);

var 1..11: numSlices_2700; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_2700;
constraint numSlices_2700 = [Add_2698, 11][inumSlices_2700];

var bool: equals_numSlices_2700__8 = (numSlices_2700 = 8);

var 1..12: numSlices_2757; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_2757;
constraint numSlices_2757 = [Add_2755, 12][inumSlices_2757];

var bool: equals_numSlices_2757__8 = (numSlices_2757 = 8);

var 1..13: numSlices_3518; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_3518;
constraint numSlices_3518 = [Add_3516, 13][inumSlices_3518];

var bool: equals_numSlices_3518__8 = (numSlices_3518 = 8);

var 1..14: numSlices_3575; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_3575;
constraint numSlices_3575 = [Add_3573, 14][inumSlices_3575];

var bool: equals_numSlices_3575__8 = (numSlices_3575 = 8);

var 1..15: numSlices_3632; %ref ref (Literal: 0 [0]).pizza -30.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).pizza -30.numSlices -13
var 1..1: inumSlices_3632;
constraint numSlices_3632 = [Add_3630, 15][inumSlices_3632];

var bool: equals_numSlices_3632__8 = (numSlices_3632 = 8);

var 0..5: numSlices_3722; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..6: inumSlices_3722;
constraint [23, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, 23][inumSlices_3722] = 23;
constraint (true) -> inumSlices_3722 >= 1;
constraint ((23 = pizza_1539)) -> inumSlices_3722 >= 2;
constraint ((23 = pizza_1590)) -> inumSlices_3722 >= 3;
constraint ((23 = pizza_1641)) -> inumSlices_3722 >= 4;
constraint ((23 = pizza_1692)) -> inumSlices_3722 >= 5;
constraint ((23 = pizza_1743)) -> inumSlices_3722 >= 6;
constraint numSlices_3722 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, 5][inumSlices_3722];

var bool: Greater_3724 = (numSlices_3722 > 0);

var {0,4,8,12,16,20}: slicesCost_3731; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_3731;
constraint slicesCost_3731 = [Multiply_3728, 20][islicesCost_3731];
constraint Greater_3724 -> (islicesCost_3731 < 2);
var bool: Greater_3733 = (slicesCost_3731 > 11);
var 0..15: numSlices_3788; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..12: inumSlices_3788;
constraint [29, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 29][inumSlices_3788] = 29;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3788];
constraint (true) -> inumSlices_3788 >= 1;
constraint ((29 = pizza_1539)) -> inumSlices_3788 >= 2;
constraint ((29 = pizza_1590)) -> inumSlices_3788 >= 3;
constraint ((29 = pizza_1641)) -> inumSlices_3788 >= 4;
constraint ((29 = pizza_1692)) -> inumSlices_3788 >= 5;
constraint ((29 = pizza_1743)) -> inumSlices_3788 >= 6;
constraint ((29 = pizza_3505)) -> inumSlices_3788 >= 7;
constraint ((equals_numSlices_3518__8 /\ (29 = pizza_3505))) -> inumSlices_3788 >= 8;
constraint ((29 = pizza_3562)) -> inumSlices_3788 >= 9;
constraint ((equals_numSlices_3575__8 /\ (29 = pizza_3562))) -> inumSlices_3788 >= 10;
constraint ((29 = pizza_3619)) -> inumSlices_3788 >= 11;
constraint ((equals_numSlices_3632__8 /\ (29 = pizza_3619))) -> inumSlices_3788 >= 12;
constraint numSlices_3788 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3788];

var bool: Greater_3790 = (numSlices_3788 > 0);

var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_3797; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_3797;
constraint slicesCost_3797 = [Multiply_3794, 75][islicesCost_3797];
constraint Greater_3790 -> (islicesCost_3797 < 2);
var bool: Greater_3799 = (slicesCost_3797 > 10);
var 0..15: numSlices_3854; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..12: inumSlices_3854;
constraint [35, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 35][inumSlices_3854] = 35;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3854];
constraint (true) -> inumSlices_3854 >= 1;
constraint ((35 = pizza_1539)) -> inumSlices_3854 >= 2;
constraint ((35 = pizza_1590)) -> inumSlices_3854 >= 3;
constraint ((35 = pizza_1641)) -> inumSlices_3854 >= 4;
constraint ((35 = pizza_1692)) -> inumSlices_3854 >= 5;
constraint ((35 = pizza_1743)) -> inumSlices_3854 >= 6;
constraint ((35 = pizza_3505)) -> inumSlices_3854 >= 7;
constraint ((equals_numSlices_3518__8 /\ (35 = pizza_3505))) -> inumSlices_3854 >= 8;
constraint ((35 = pizza_3562)) -> inumSlices_3854 >= 9;
constraint ((equals_numSlices_3575__8 /\ (35 = pizza_3562))) -> inumSlices_3854 >= 10;
constraint ((35 = pizza_3619)) -> inumSlices_3854 >= 11;
constraint ((equals_numSlices_3632__8 /\ (35 = pizza_3619))) -> inumSlices_3854 >= 12;
constraint numSlices_3854 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3854];

var bool: Greater_3856 = (numSlices_3854 > 0);

var {0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60}: slicesCost_3863; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_3863;
constraint slicesCost_3863 = [Multiply_3860, 60][islicesCost_3863];
constraint Greater_3856 -> (islicesCost_3863 < 2);
var bool: Greater_3865 = (slicesCost_3863 > 14);
var 0..15: numSlices_3920; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..12: inumSlices_3920;
constraint [41, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 41][inumSlices_3920] = 41;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3920];
constraint (true) -> inumSlices_3920 >= 1;
constraint ((41 = pizza_1539)) -> inumSlices_3920 >= 2;
constraint ((41 = pizza_1590)) -> inumSlices_3920 >= 3;
constraint ((41 = pizza_1641)) -> inumSlices_3920 >= 4;
constraint ((41 = pizza_1692)) -> inumSlices_3920 >= 5;
constraint ((41 = pizza_1743)) -> inumSlices_3920 >= 6;
constraint ((41 = pizza_3505)) -> inumSlices_3920 >= 7;
constraint ((equals_numSlices_3518__8 /\ (41 = pizza_3505))) -> inumSlices_3920 >= 8;
constraint ((41 = pizza_3562)) -> inumSlices_3920 >= 9;
constraint ((equals_numSlices_3575__8 /\ (41 = pizza_3562))) -> inumSlices_3920 >= 10;
constraint ((41 = pizza_3619)) -> inumSlices_3920 >= 11;
constraint ((equals_numSlices_3632__8 /\ (41 = pizza_3619))) -> inumSlices_3920 >= 12;
constraint numSlices_3920 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3920];

var bool: Greater_3922 = (numSlices_3920 > 0);

var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_3929; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_3929;
constraint slicesCost_3929 = [Multiply_3926, 75][islicesCost_3929];
constraint Greater_3922 -> (islicesCost_3929 < 2);
var bool: Greater_3931 = (slicesCost_3929 > 16);
var 0..15: numSlices_3986; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..24: inumSlices_3986;
constraint [47, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 47][inumSlices_3986] = 47;
constraint [true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_3986];
constraint (true) -> inumSlices_3986 >= 1;
constraint ((47 = pizza_1539)) -> inumSlices_3986 >= 2;
constraint ((47 = pizza_1590)) -> inumSlices_3986 >= 3;
constraint ((47 = pizza_1641)) -> inumSlices_3986 >= 4;
constraint ((47 = pizza_1692)) -> inumSlices_3986 >= 5;
constraint ((47 = pizza_1743)) -> inumSlices_3986 >= 6;
constraint ((47 = pizza_2414)) -> inumSlices_3986 >= 7;
constraint ((47 = pizza_2465)) -> inumSlices_3986 >= 8;
constraint ((47 = pizza_2516)) -> inumSlices_3986 >= 9;
constraint ((equals_numSlices_2529__8 /\ (47 = pizza_2516))) -> inumSlices_3986 >= 10;
constraint ((47 = pizza_2573)) -> inumSlices_3986 >= 11;
constraint ((equals_numSlices_2586__8 /\ (47 = pizza_2573))) -> inumSlices_3986 >= 12;
constraint ((47 = pizza_2630)) -> inumSlices_3986 >= 13;
constraint ((equals_numSlices_2643__8 /\ (47 = pizza_2630))) -> inumSlices_3986 >= 14;
constraint ((47 = pizza_2687)) -> inumSlices_3986 >= 15;
constraint ((equals_numSlices_2700__8 /\ (47 = pizza_2687))) -> inumSlices_3986 >= 16;
constraint ((47 = pizza_2744)) -> inumSlices_3986 >= 17;
constraint ((equals_numSlices_2757__8 /\ (47 = pizza_2744))) -> inumSlices_3986 >= 18;
constraint ((47 = pizza_3505)) -> inumSlices_3986 >= 19;
constraint ((equals_numSlices_3518__8 /\ (47 = pizza_3505))) -> inumSlices_3986 >= 20;
constraint ((47 = pizza_3562)) -> inumSlices_3986 >= 21;
constraint ((equals_numSlices_3575__8 /\ (47 = pizza_3562))) -> inumSlices_3986 >= 22;
constraint ((47 = pizza_3619)) -> inumSlices_3986 >= 23;
constraint ((equals_numSlices_3632__8 /\ (47 = pizza_3619))) -> inumSlices_3986 >= 24;
constraint numSlices_3986 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_3986];

var bool: Greater_3988 = (numSlices_3986 > 0);

var {0,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45}: slicesCost_3995; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_3995;
constraint slicesCost_3995 = [Multiply_3992, 45][islicesCost_3995];
constraint Greater_3988 -> (islicesCost_3995 < 2);
var bool: Greater_3997 = (slicesCost_3995 > 10);
var 0..15: numSlices_4052; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..12: inumSlices_4052;
constraint [53, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 53][inumSlices_4052] = 53;
constraint [true, true, true, true, true, true, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4052];
constraint (true) -> inumSlices_4052 >= 1;
constraint ((53 = pizza_1539)) -> inumSlices_4052 >= 2;
constraint ((53 = pizza_1590)) -> inumSlices_4052 >= 3;
constraint ((53 = pizza_1641)) -> inumSlices_4052 >= 4;
constraint ((53 = pizza_1692)) -> inumSlices_4052 >= 5;
constraint ((53 = pizza_1743)) -> inumSlices_4052 >= 6;
constraint ((53 = pizza_3505)) -> inumSlices_4052 >= 7;
constraint ((equals_numSlices_3518__8 /\ (53 = pizza_3505))) -> inumSlices_4052 >= 8;
constraint ((53 = pizza_3562)) -> inumSlices_4052 >= 9;
constraint ((equals_numSlices_3575__8 /\ (53 = pizza_3562))) -> inumSlices_4052 >= 10;
constraint ((53 = pizza_3619)) -> inumSlices_4052 >= 11;
constraint ((equals_numSlices_3632__8 /\ (53 = pizza_3619))) -> inumSlices_4052 >= 12;
constraint numSlices_4052 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4052];

var bool: Greater_4054 = (numSlices_4052 > 0);

var {0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60}: slicesCost_4061; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_4061;
constraint slicesCost_4061 = [Multiply_4058, 60][islicesCost_4061];
constraint Greater_4054 -> (islicesCost_4061 < 2);
var bool: Greater_4063 = (slicesCost_4061 > 15);
var 0..15: numSlices_4118; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..19: inumSlices_4118;
constraint [59, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 59][inumSlices_4118] = 59;
constraint [true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4118];
constraint (true) -> inumSlices_4118 >= 1;
constraint ((59 = pizza_2414)) -> inumSlices_4118 >= 2;
constraint ((59 = pizza_2465)) -> inumSlices_4118 >= 3;
constraint ((59 = pizza_2516)) -> inumSlices_4118 >= 4;
constraint ((equals_numSlices_2529__8 /\ (59 = pizza_2516))) -> inumSlices_4118 >= 5;
constraint ((59 = pizza_2573)) -> inumSlices_4118 >= 6;
constraint ((equals_numSlices_2586__8 /\ (59 = pizza_2573))) -> inumSlices_4118 >= 7;
constraint ((59 = pizza_2630)) -> inumSlices_4118 >= 8;
constraint ((equals_numSlices_2643__8 /\ (59 = pizza_2630))) -> inumSlices_4118 >= 9;
constraint ((59 = pizza_2687)) -> inumSlices_4118 >= 10;
constraint ((equals_numSlices_2700__8 /\ (59 = pizza_2687))) -> inumSlices_4118 >= 11;
constraint ((59 = pizza_2744)) -> inumSlices_4118 >= 12;
constraint ((equals_numSlices_2757__8 /\ (59 = pizza_2744))) -> inumSlices_4118 >= 13;
constraint ((59 = pizza_3505)) -> inumSlices_4118 >= 14;
constraint ((equals_numSlices_3518__8 /\ (59 = pizza_3505))) -> inumSlices_4118 >= 15;
constraint ((59 = pizza_3562)) -> inumSlices_4118 >= 16;
constraint ((equals_numSlices_3575__8 /\ (59 = pizza_3562))) -> inumSlices_4118 >= 17;
constraint ((59 = pizza_3619)) -> inumSlices_4118 >= 18;
constraint ((equals_numSlices_3632__8 /\ (59 = pizza_3619))) -> inumSlices_4118 >= 19;
constraint numSlices_4118 = [0, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4118];

var bool: Greater_4120 = (numSlices_4118 > 0);

var {0,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45}: slicesCost_4127; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_4127;
constraint slicesCost_4127 = [Multiply_4124, 45][islicesCost_4127];
constraint Greater_4120 -> (islicesCost_4127 < 2);
var bool: Greater_4129 = (slicesCost_4127 > 11);
var 0..15: numSlices_4184; %ref ref (Literal: 0 [0]).item -35.numSlices -13
% doing constraints for lookup query: ref ref (Literal: 0 [0]).item -35.numSlices -13
var 1..24: inumSlices_4184;
constraint [65, pizza_1539, pizza_1590, pizza_1641, pizza_1692, pizza_1743, pizza_2414, pizza_2465, pizza_2516, pizza_2516, pizza_2573, pizza_2573, pizza_2630, pizza_2630, pizza_2687, pizza_2687, pizza_2744, pizza_2744, pizza_3505, pizza_3505, pizza_3562, pizza_3562, pizza_3619, pizza_3619, 65][inumSlices_4184] = 65;
constraint [true, true, true, true, true, true, true, true, true, equals_numSlices_2529__8, true, equals_numSlices_2586__8, true, equals_numSlices_2643__8, true, equals_numSlices_2700__8, true, equals_numSlices_2757__8, true, equals_numSlices_3518__8, true, equals_numSlices_3575__8, true, equals_numSlices_3632__8, true][inumSlices_4184];
constraint (true) -> inumSlices_4184 >= 1;
constraint ((65 = pizza_1539)) -> inumSlices_4184 >= 2;
constraint ((65 = pizza_1590)) -> inumSlices_4184 >= 3;
constraint ((65 = pizza_1641)) -> inumSlices_4184 >= 4;
constraint ((65 = pizza_1692)) -> inumSlices_4184 >= 5;
constraint ((65 = pizza_1743)) -> inumSlices_4184 >= 6;
constraint ((65 = pizza_2414)) -> inumSlices_4184 >= 7;
constraint ((65 = pizza_2465)) -> inumSlices_4184 >= 8;
constraint ((65 = pizza_2516)) -> inumSlices_4184 >= 9;
constraint ((equals_numSlices_2529__8 /\ (65 = pizza_2516))) -> inumSlices_4184 >= 10;
constraint ((65 = pizza_2573)) -> inumSlices_4184 >= 11;
constraint ((equals_numSlices_2586__8 /\ (65 = pizza_2573))) -> inumSlices_4184 >= 12;
constraint ((65 = pizza_2630)) -> inumSlices_4184 >= 13;
constraint ((equals_numSlices_2643__8 /\ (65 = pizza_2630))) -> inumSlices_4184 >= 14;
constraint ((65 = pizza_2687)) -> inumSlices_4184 >= 15;
constraint ((equals_numSlices_2700__8 /\ (65 = pizza_2687))) -> inumSlices_4184 >= 16;
constraint ((65 = pizza_2744)) -> inumSlices_4184 >= 17;
constraint ((equals_numSlices_2757__8 /\ (65 = pizza_2744))) -> inumSlices_4184 >= 18;
constraint ((65 = pizza_3505)) -> inumSlices_4184 >= 19;
constraint ((equals_numSlices_3518__8 /\ (65 = pizza_3505))) -> inumSlices_4184 >= 20;
constraint ((65 = pizza_3562)) -> inumSlices_4184 >= 21;
constraint ((equals_numSlices_3575__8 /\ (65 = pizza_3562))) -> inumSlices_4184 >= 22;
constraint ((65 = pizza_3619)) -> inumSlices_4184 >= 23;
constraint ((equals_numSlices_3632__8 /\ (65 = pizza_3619))) -> inumSlices_4184 >= 24;
constraint numSlices_4184 = [0, 1, Add_1601, Add_1652, Add_1703, Add_1754, Add_2425, Add_2476, Add_2527, 0, Add_2584, 0, Add_2641, 0, Add_2698, 0, Add_2755, 0, Add_3516, 0, Add_3573, 0, Add_3630, 0, 15][inumSlices_4184];

var bool: Greater_4186 = (numSlices_4184 > 0);

var {0,5,10,15,20,25,30,35,40,45,50,55,60,65,70,75}: slicesCost_4193; %ref (Literal: 0 [0]).slicesCost -38
% doing constraints for lookup query: ref (Literal: 0 [0]).slicesCost -38
var 1..2: islicesCost_4193;
constraint slicesCost_4193 = [Multiply_4190, 75][islicesCost_4193];
constraint Greater_4186 -> (islicesCost_4193 < 2);
var bool: Greater_4195 = (slicesCost_4193 > 16);
solve :: seq_search([
		 int_search([chooseobj_1530, chooseobj_1581, chooseobj_1632, chooseobj_1683, chooseobj_1734, chooseobj_2405, chooseobj_2456, chooseobj_2507, chooseobj_2564, chooseobj_2621, chooseobj_2678, chooseobj_2735, chooseobj_3496, chooseobj_3553, chooseobj_3610],input_order,indomain_min,complete),
		bool_search([equals_numSlices_2529__8, equals_numSlices_2586__8, equals_numSlices_2643__8, equals_numSlices_2700__8, equals_numSlices_2757__8, equals_numSlices_3518__8, equals_numSlices_3575__8, equals_numSlices_3632__8, Greater_3724, Greater_3733, Greater_3790, Greater_3799, Greater_3856, Greater_3865, Greater_3922, Greater_3931, Greater_3988, Greater_3997, Greater_4054, Greater_4063, Greater_4120, Greater_4129, Greater_4186, Greater_4195], input_order, indomain_max, complete),
		int_search([chooseobj_1530, pizza_1539, ipizza_1539, chooseobj_1581, pizza_1590, ipizza_1590, numSlices_1599, inumSlices_1599, Add_1601, chooseobj_1632, pizza_1641, ipizza_1641, numSlices_1650, inumSlices_1650, Add_1652, chooseobj_1683, pizza_1692, ipizza_1692, numSlices_1701, inumSlices_1701, Add_1703, chooseobj_1734, pizza_1743, ipizza_1743, numSlices_1752, inumSlices_1752, Add_1754, chooseobj_2405, pizza_2414, ipizza_2414, numSlices_2423, inumSlices_2423, Add_2425, chooseobj_2456, pizza_2465, ipizza_2465, numSlices_2474, inumSlices_2474, Add_2476, chooseobj_2507, pizza_2516, ipizza_2516, numSlices_2525, inumSlices_2525, Add_2527, chooseobj_2564, pizza_2573, ipizza_2573, numSlices_2582, inumSlices_2582, Add_2584, fullPizzas_2592, ifullPizzas_2592, Add_2594, chooseobj_2621, pizza_2630, ipizza_2630, numSlices_2639, inumSlices_2639, Add_2641, fullPizzas_2649, ifullPizzas_2649, Add_2651, chooseobj_2678, pizza_2687, ipizza_2687, numSlices_2696, inumSlices_2696, Add_2698, fullPizzas_2706, ifullPizzas_2706, Add_2708, chooseobj_2735, pizza_2744, ipizza_2744, numSlices_2753, inumSlices_2753, Add_2755, fullPizzas_2763, ifullPizzas_2763, Add_2765, chooseobj_3496, pizza_3505, ipizza_3505, numSlices_3514, inumSlices_3514, Add_3516, fullPizzas_3524, ifullPizzas_3524, Add_3526, chooseobj_3553, pizza_3562, ipizza_3562, numSlices_3571, inumSlices_3571, Add_3573, fullPizzas_3581, ifullPizzas_3581, Add_3583, chooseobj_3610, pizza_3619, ipizza_3619, numSlices_3628, inumSlices_3628, Add_3630, fullPizzas_3638, ifullPizzas_3638, Add_3640, numSlices_3726, inumSlices_3726, Multiply_3728, slicesCost_3739, islicesCost_3739, Add_3740, cost_3743, icost_3743, ret_getCost_3747, iret_getCost_3747, Add_3748, totalcost_3772, itotalcost_3772, fullPizzas_3783, ifullPizzas_3783, Multiply_3785, numSlices_3792, inumSlices_3792, Multiply_3794, cost_3804, icost_3804, slicesCost_3805, islicesCost_3805, Add_3806, cost_3809, icost_3809, ret_getCost_3813, iret_getCost_3813, Add_3814, totalcost_3838, itotalcost_3838, fullPizzas_3849, ifullPizzas_3849, Multiply_3851, numSlices_3858, inumSlices_3858, Multiply_3860, cost_3870, icost_3870, slicesCost_3871, islicesCost_3871, Add_3872, cost_3875, icost_3875, ret_getCost_3879, iret_getCost_3879, Add_3880, totalcost_3904, itotalcost_3904, fullPizzas_3915, ifullPizzas_3915, Multiply_3917, numSlices_3924, inumSlices_3924, Multiply_3926, cost_3936, icost_3936, slicesCost_3937, islicesCost_3937, Add_3938, cost_3941, icost_3941, ret_getCost_3945, iret_getCost_3945, Add_3946, totalcost_3970, itotalcost_3970, fullPizzas_3981, ifullPizzas_3981, Multiply_3983, numSlices_3990, inumSlices_3990, Multiply_3992, cost_4002, icost_4002, slicesCost_4003, islicesCost_4003, Add_4004, cost_4007, icost_4007, ret_getCost_4011, iret_getCost_4011, Add_4012, totalcost_4036, itotalcost_4036, fullPizzas_4047, ifullPizzas_4047, Multiply_4049, numSlices_4056, inumSlices_4056, Multiply_4058, cost_4068, icost_4068, slicesCost_4069, islicesCost_4069, Add_4070, cost_4073, icost_4073, ret_getCost_4077, iret_getCost_4077, Add_4078, totalcost_4102, itotalcost_4102, fullPizzas_4113, ifullPizzas_4113, Multiply_4115, numSlices_4122, inumSlices_4122, Multiply_4124, cost_4134, icost_4134, slicesCost_4135, islicesCost_4135, Add_4136, cost_4139, icost_4139, ret_getCost_4143, iret_getCost_4143, Add_4144, totalcost_4168, itotalcost_4168, fullPizzas_4179, ifullPizzas_4179, Multiply_4181, numSlices_4188, inumSlices_4188, Multiply_4190, cost_4200, icost_4200, slicesCost_4201, islicesCost_4201, Add_4202, cost_4205, icost_4205, ret_getCost_4209, iret_getCost_4209, Add_4210, totalcost_4214, itotalcost_4214, ret_totalCost_4218, iret_totalCost_4218, objective, iobjective, numSlices_2529, inumSlices_2529, numSlices_2586, inumSlices_2586, numSlices_2643, inumSlices_2643, numSlices_2700, inumSlices_2700, numSlices_2757, inumSlices_2757, numSlices_3518, inumSlices_3518, numSlices_3575, inumSlices_3575, numSlices_3632, inumSlices_3632, numSlices_3722, inumSlices_3722, slicesCost_3731, islicesCost_3731, numSlices_3788, inumSlices_3788, slicesCost_3797, islicesCost_3797, numSlices_3854, inumSlices_3854, slicesCost_3863, islicesCost_3863, numSlices_3920, inumSlices_3920, slicesCost_3929, islicesCost_3929, numSlices_3986, inumSlices_3986, slicesCost_3995, islicesCost_3995, numSlices_4052, inumSlices_4052, slicesCost_4061, islicesCost_4061, numSlices_4118, inumSlices_4118, slicesCost_4127, islicesCost_4127, numSlices_4184, inumSlices_4184, slicesCost_4193, islicesCost_4193], first_fail, indomain_min, complete),
	])
	minimize objective;

output [
	"constraint equals_numSlices_2529__8 = \(equals_numSlices_2529__8);\n",
	"constraint equals_numSlices_2586__8 = \(equals_numSlices_2586__8);\n",
	"constraint equals_numSlices_2643__8 = \(equals_numSlices_2643__8);\n",
	"constraint equals_numSlices_2700__8 = \(equals_numSlices_2700__8);\n",
	"constraint equals_numSlices_2757__8 = \(equals_numSlices_2757__8);\n",
	"constraint equals_numSlices_3518__8 = \(equals_numSlices_3518__8);\n",
	"constraint equals_numSlices_3575__8 = \(equals_numSlices_3575__8);\n",
	"constraint equals_numSlices_3632__8 = \(equals_numSlices_3632__8);\n",
	"constraint Greater_3724 = \(Greater_3724);\n",
	"constraint Greater_3733 = \(Greater_3733);\n",
	"constraint Greater_3790 = \(Greater_3790);\n",
	"constraint Greater_3799 = \(Greater_3799);\n",
	"constraint Greater_3856 = \(Greater_3856);\n",
	"constraint Greater_3865 = \(Greater_3865);\n",
	"constraint Greater_3922 = \(Greater_3922);\n",
	"constraint Greater_3931 = \(Greater_3931);\n",
	"constraint Greater_3988 = \(Greater_3988);\n",
	"constraint Greater_3997 = \(Greater_3997);\n",
	"constraint Greater_4054 = \(Greater_4054);\n",
	"constraint Greater_4063 = \(Greater_4063);\n",
	"constraint Greater_4120 = \(Greater_4120);\n",
	"constraint Greater_4129 = \(Greater_4129);\n",
	"constraint Greater_4186 = \(Greater_4186);\n",
	"constraint Greater_4195 = \(Greater_4195);\n",
	"chooseobj_1530 = \(chooseobj_1530);\n",
	"pizza_1539 = \(pizza_1539);\n",
	"ipizza_1539 = \(ipizza_1539);\n",
	"chooseobj_1581 = \(chooseobj_1581);\n",
	"pizza_1590 = \(pizza_1590);\n",
	"ipizza_1590 = \(ipizza_1590);\n",
	"numSlices_1599 = \(numSlices_1599);\n",
	"inumSlices_1599 = \(inumSlices_1599);\n",
	"constraint Add_1601 = \(Add_1601);\n",
	"chooseobj_1632 = \(chooseobj_1632);\n",
	"pizza_1641 = \(pizza_1641);\n",
	"ipizza_1641 = \(ipizza_1641);\n",
	"numSlices_1650 = \(numSlices_1650);\n",
	"inumSlices_1650 = \(inumSlices_1650);\n",
	"constraint Add_1652 = \(Add_1652);\n",
	"chooseobj_1683 = \(chooseobj_1683);\n",
	"pizza_1692 = \(pizza_1692);\n",
	"ipizza_1692 = \(ipizza_1692);\n",
	"numSlices_1701 = \(numSlices_1701);\n",
	"inumSlices_1701 = \(inumSlices_1701);\n",
	"constraint Add_1703 = \(Add_1703);\n",
	"chooseobj_1734 = \(chooseobj_1734);\n",
	"pizza_1743 = \(pizza_1743);\n",
	"ipizza_1743 = \(ipizza_1743);\n",
	"numSlices_1752 = \(numSlices_1752);\n",
	"inumSlices_1752 = \(inumSlices_1752);\n",
	"constraint Add_1754 = \(Add_1754);\n",
	"chooseobj_2405 = \(chooseobj_2405);\n",
	"pizza_2414 = \(pizza_2414);\n",
	"ipizza_2414 = \(ipizza_2414);\n",
	"numSlices_2423 = \(numSlices_2423);\n",
	"inumSlices_2423 = \(inumSlices_2423);\n",
	"constraint Add_2425 = \(Add_2425);\n",
	"chooseobj_2456 = \(chooseobj_2456);\n",
	"pizza_2465 = \(pizza_2465);\n",
	"ipizza_2465 = \(ipizza_2465);\n",
	"numSlices_2474 = \(numSlices_2474);\n",
	"inumSlices_2474 = \(inumSlices_2474);\n",
	"constraint Add_2476 = \(Add_2476);\n",
	"chooseobj_2507 = \(chooseobj_2507);\n",
	"pizza_2516 = \(pizza_2516);\n",
	"ipizza_2516 = \(ipizza_2516);\n",
	"numSlices_2525 = \(numSlices_2525);\n",
	"inumSlices_2525 = \(inumSlices_2525);\n",
	"constraint Add_2527 = \(Add_2527);\n",
	"chooseobj_2564 = \(chooseobj_2564);\n",
	"pizza_2573 = \(pizza_2573);\n",
	"ipizza_2573 = \(ipizza_2573);\n",
	"numSlices_2582 = \(numSlices_2582);\n",
	"inumSlices_2582 = \(inumSlices_2582);\n",
	"constraint Add_2584 = \(Add_2584);\n",
	"fullPizzas_2592 = \(fullPizzas_2592);\n",
	"ifullPizzas_2592 = \(ifullPizzas_2592);\n",
	"constraint Add_2594 = \(Add_2594);\n",
	"chooseobj_2621 = \(chooseobj_2621);\n",
	"pizza_2630 = \(pizza_2630);\n",
	"ipizza_2630 = \(ipizza_2630);\n",
	"numSlices_2639 = \(numSlices_2639);\n",
	"inumSlices_2639 = \(inumSlices_2639);\n",
	"constraint Add_2641 = \(Add_2641);\n",
	"fullPizzas_2649 = \(fullPizzas_2649);\n",
	"ifullPizzas_2649 = \(ifullPizzas_2649);\n",
	"constraint Add_2651 = \(Add_2651);\n",
	"chooseobj_2678 = \(chooseobj_2678);\n",
	"pizza_2687 = \(pizza_2687);\n",
	"ipizza_2687 = \(ipizza_2687);\n",
	"numSlices_2696 = \(numSlices_2696);\n",
	"inumSlices_2696 = \(inumSlices_2696);\n",
	"constraint Add_2698 = \(Add_2698);\n",
	"fullPizzas_2706 = \(fullPizzas_2706);\n",
	"ifullPizzas_2706 = \(ifullPizzas_2706);\n",
	"constraint Add_2708 = \(Add_2708);\n",
	"chooseobj_2735 = \(chooseobj_2735);\n",
	"pizza_2744 = \(pizza_2744);\n",
	"ipizza_2744 = \(ipizza_2744);\n",
	"numSlices_2753 = \(numSlices_2753);\n",
	"inumSlices_2753 = \(inumSlices_2753);\n",
	"constraint Add_2755 = \(Add_2755);\n",
	"fullPizzas_2763 = \(fullPizzas_2763);\n",
	"ifullPizzas_2763 = \(ifullPizzas_2763);\n",
	"constraint Add_2765 = \(Add_2765);\n",
	"chooseobj_3496 = \(chooseobj_3496);\n",
	"pizza_3505 = \(pizza_3505);\n",
	"ipizza_3505 = \(ipizza_3505);\n",
	"numSlices_3514 = \(numSlices_3514);\n",
	"inumSlices_3514 = \(inumSlices_3514);\n",
	"constraint Add_3516 = \(Add_3516);\n",
	"fullPizzas_3524 = \(fullPizzas_3524);\n",
	"ifullPizzas_3524 = \(ifullPizzas_3524);\n",
	"constraint Add_3526 = \(Add_3526);\n",
	"chooseobj_3553 = \(chooseobj_3553);\n",
	"pizza_3562 = \(pizza_3562);\n",
	"ipizza_3562 = \(ipizza_3562);\n",
	"numSlices_3571 = \(numSlices_3571);\n",
	"inumSlices_3571 = \(inumSlices_3571);\n",
	"constraint Add_3573 = \(Add_3573);\n",
	"fullPizzas_3581 = \(fullPizzas_3581);\n",
	"ifullPizzas_3581 = \(ifullPizzas_3581);\n",
	"constraint Add_3583 = \(Add_3583);\n",
	"chooseobj_3610 = \(chooseobj_3610);\n",
	"pizza_3619 = \(pizza_3619);\n",
	"ipizza_3619 = \(ipizza_3619);\n",
	"numSlices_3628 = \(numSlices_3628);\n",
	"inumSlices_3628 = \(inumSlices_3628);\n",
	"constraint Add_3630 = \(Add_3630);\n",
	"fullPizzas_3638 = \(fullPizzas_3638);\n",
	"ifullPizzas_3638 = \(ifullPizzas_3638);\n",
	"constraint Add_3640 = \(Add_3640);\n",
	"numSlices_3726 = \(numSlices_3726);\n",
	"inumSlices_3726 = \(inumSlices_3726);\n",
	"constraint Multiply_3728 = \(Multiply_3728);\n",
	"slicesCost_3739 = \(slicesCost_3739);\n",
	"islicesCost_3739 = \(islicesCost_3739);\n",
	"constraint Add_3740 = \(Add_3740);\n",
	"cost_3743 = \(cost_3743);\n",
	"icost_3743 = \(icost_3743);\n",
	"ret_getCost_3747 = \(ret_getCost_3747);\n",
	"iret_getCost_3747 = \(iret_getCost_3747);\n",
	"constraint Add_3748 = \(Add_3748);\n",
	"totalcost_3772 = \(totalcost_3772);\n",
	"itotalcost_3772 = \(itotalcost_3772);\n",
	"fullPizzas_3783 = \(fullPizzas_3783);\n",
	"ifullPizzas_3783 = \(ifullPizzas_3783);\n",
	"constraint Multiply_3785 = \(Multiply_3785);\n",
	"numSlices_3792 = \(numSlices_3792);\n",
	"inumSlices_3792 = \(inumSlices_3792);\n",
	"constraint Multiply_3794 = \(Multiply_3794);\n",
	"cost_3804 = \(cost_3804);\n",
	"icost_3804 = \(icost_3804);\n",
	"slicesCost_3805 = \(slicesCost_3805);\n",
	"islicesCost_3805 = \(islicesCost_3805);\n",
	"constraint Add_3806 = \(Add_3806);\n",
	"cost_3809 = \(cost_3809);\n",
	"icost_3809 = \(icost_3809);\n",
	"ret_getCost_3813 = \(ret_getCost_3813);\n",
	"iret_getCost_3813 = \(iret_getCost_3813);\n",
	"constraint Add_3814 = \(Add_3814);\n",
	"totalcost_3838 = \(totalcost_3838);\n",
	"itotalcost_3838 = \(itotalcost_3838);\n",
	"fullPizzas_3849 = \(fullPizzas_3849);\n",
	"ifullPizzas_3849 = \(ifullPizzas_3849);\n",
	"constraint Multiply_3851 = \(Multiply_3851);\n",
	"numSlices_3858 = \(numSlices_3858);\n",
	"inumSlices_3858 = \(inumSlices_3858);\n",
	"constraint Multiply_3860 = \(Multiply_3860);\n",
	"cost_3870 = \(cost_3870);\n",
	"icost_3870 = \(icost_3870);\n",
	"slicesCost_3871 = \(slicesCost_3871);\n",
	"islicesCost_3871 = \(islicesCost_3871);\n",
	"constraint Add_3872 = \(Add_3872);\n",
	"cost_3875 = \(cost_3875);\n",
	"icost_3875 = \(icost_3875);\n",
	"ret_getCost_3879 = \(ret_getCost_3879);\n",
	"iret_getCost_3879 = \(iret_getCost_3879);\n",
	"constraint Add_3880 = \(Add_3880);\n",
	"totalcost_3904 = \(totalcost_3904);\n",
	"itotalcost_3904 = \(itotalcost_3904);\n",
	"fullPizzas_3915 = \(fullPizzas_3915);\n",
	"ifullPizzas_3915 = \(ifullPizzas_3915);\n",
	"constraint Multiply_3917 = \(Multiply_3917);\n",
	"numSlices_3924 = \(numSlices_3924);\n",
	"inumSlices_3924 = \(inumSlices_3924);\n",
	"constraint Multiply_3926 = \(Multiply_3926);\n",
	"cost_3936 = \(cost_3936);\n",
	"icost_3936 = \(icost_3936);\n",
	"slicesCost_3937 = \(slicesCost_3937);\n",
	"islicesCost_3937 = \(islicesCost_3937);\n",
	"constraint Add_3938 = \(Add_3938);\n",
	"cost_3941 = \(cost_3941);\n",
	"icost_3941 = \(icost_3941);\n",
	"ret_getCost_3945 = \(ret_getCost_3945);\n",
	"iret_getCost_3945 = \(iret_getCost_3945);\n",
	"constraint Add_3946 = \(Add_3946);\n",
	"totalcost_3970 = \(totalcost_3970);\n",
	"itotalcost_3970 = \(itotalcost_3970);\n",
	"fullPizzas_3981 = \(fullPizzas_3981);\n",
	"ifullPizzas_3981 = \(ifullPizzas_3981);\n",
	"constraint Multiply_3983 = \(Multiply_3983);\n",
	"numSlices_3990 = \(numSlices_3990);\n",
	"inumSlices_3990 = \(inumSlices_3990);\n",
	"constraint Multiply_3992 = \(Multiply_3992);\n",
	"cost_4002 = \(cost_4002);\n",
	"icost_4002 = \(icost_4002);\n",
	"slicesCost_4003 = \(slicesCost_4003);\n",
	"islicesCost_4003 = \(islicesCost_4003);\n",
	"constraint Add_4004 = \(Add_4004);\n",
	"cost_4007 = \(cost_4007);\n",
	"icost_4007 = \(icost_4007);\n",
	"ret_getCost_4011 = \(ret_getCost_4011);\n",
	"iret_getCost_4011 = \(iret_getCost_4011);\n",
	"constraint Add_4012 = \(Add_4012);\n",
	"totalcost_4036 = \(totalcost_4036);\n",
	"itotalcost_4036 = \(itotalcost_4036);\n",
	"fullPizzas_4047 = \(fullPizzas_4047);\n",
	"ifullPizzas_4047 = \(ifullPizzas_4047);\n",
	"constraint Multiply_4049 = \(Multiply_4049);\n",
	"numSlices_4056 = \(numSlices_4056);\n",
	"inumSlices_4056 = \(inumSlices_4056);\n",
	"constraint Multiply_4058 = \(Multiply_4058);\n",
	"cost_4068 = \(cost_4068);\n",
	"icost_4068 = \(icost_4068);\n",
	"slicesCost_4069 = \(slicesCost_4069);\n",
	"islicesCost_4069 = \(islicesCost_4069);\n",
	"constraint Add_4070 = \(Add_4070);\n",
	"cost_4073 = \(cost_4073);\n",
	"icost_4073 = \(icost_4073);\n",
	"ret_getCost_4077 = \(ret_getCost_4077);\n",
	"iret_getCost_4077 = \(iret_getCost_4077);\n",
	"constraint Add_4078 = \(Add_4078);\n",
	"totalcost_4102 = \(totalcost_4102);\n",
	"itotalcost_4102 = \(itotalcost_4102);\n",
	"fullPizzas_4113 = \(fullPizzas_4113);\n",
	"ifullPizzas_4113 = \(ifullPizzas_4113);\n",
	"constraint Multiply_4115 = \(Multiply_4115);\n",
	"numSlices_4122 = \(numSlices_4122);\n",
	"inumSlices_4122 = \(inumSlices_4122);\n",
	"constraint Multiply_4124 = \(Multiply_4124);\n",
	"cost_4134 = \(cost_4134);\n",
	"icost_4134 = \(icost_4134);\n",
	"slicesCost_4135 = \(slicesCost_4135);\n",
	"islicesCost_4135 = \(islicesCost_4135);\n",
	"constraint Add_4136 = \(Add_4136);\n",
	"cost_4139 = \(cost_4139);\n",
	"icost_4139 = \(icost_4139);\n",
	"ret_getCost_4143 = \(ret_getCost_4143);\n",
	"iret_getCost_4143 = \(iret_getCost_4143);\n",
	"constraint Add_4144 = \(Add_4144);\n",
	"totalcost_4168 = \(totalcost_4168);\n",
	"itotalcost_4168 = \(itotalcost_4168);\n",
	"fullPizzas_4179 = \(fullPizzas_4179);\n",
	"ifullPizzas_4179 = \(ifullPizzas_4179);\n",
	"constraint Multiply_4181 = \(Multiply_4181);\n",
	"numSlices_4188 = \(numSlices_4188);\n",
	"inumSlices_4188 = \(inumSlices_4188);\n",
	"constraint Multiply_4190 = \(Multiply_4190);\n",
	"cost_4200 = \(cost_4200);\n",
	"icost_4200 = \(icost_4200);\n",
	"slicesCost_4201 = \(slicesCost_4201);\n",
	"islicesCost_4201 = \(islicesCost_4201);\n",
	"constraint Add_4202 = \(Add_4202);\n",
	"cost_4205 = \(cost_4205);\n",
	"icost_4205 = \(icost_4205);\n",
	"ret_getCost_4209 = \(ret_getCost_4209);\n",
	"iret_getCost_4209 = \(iret_getCost_4209);\n",
	"constraint Add_4210 = \(Add_4210);\n",
	"totalcost_4214 = \(totalcost_4214);\n",
	"itotalcost_4214 = \(itotalcost_4214);\n",
	"ret_totalCost_4218 = \(ret_totalCost_4218);\n",
	"iret_totalCost_4218 = \(iret_totalCost_4218);\n",
	"iobjective = \(iobjective);\n",
	"numSlices_2529 = \(numSlices_2529);\n",
	"inumSlices_2529 = \(inumSlices_2529);\n",
	"numSlices_2586 = \(numSlices_2586);\n",
	"inumSlices_2586 = \(inumSlices_2586);\n",
	"numSlices_2643 = \(numSlices_2643);\n",
	"inumSlices_2643 = \(inumSlices_2643);\n",
	"numSlices_2700 = \(numSlices_2700);\n",
	"inumSlices_2700 = \(inumSlices_2700);\n",
	"numSlices_2757 = \(numSlices_2757);\n",
	"inumSlices_2757 = \(inumSlices_2757);\n",
	"numSlices_3518 = \(numSlices_3518);\n",
	"inumSlices_3518 = \(inumSlices_3518);\n",
	"numSlices_3575 = \(numSlices_3575);\n",
	"inumSlices_3575 = \(inumSlices_3575);\n",
	"numSlices_3632 = \(numSlices_3632);\n",
	"inumSlices_3632 = \(inumSlices_3632);\n",
	"numSlices_3722 = \(numSlices_3722);\n",
	"inumSlices_3722 = \(inumSlices_3722);\n",
	"slicesCost_3731 = \(slicesCost_3731);\n",
	"islicesCost_3731 = \(islicesCost_3731);\n",
	"numSlices_3788 = \(numSlices_3788);\n",
	"inumSlices_3788 = \(inumSlices_3788);\n",
	"slicesCost_3797 = \(slicesCost_3797);\n",
	"islicesCost_3797 = \(islicesCost_3797);\n",
	"numSlices_3854 = \(numSlices_3854);\n",
	"inumSlices_3854 = \(inumSlices_3854);\n",
	"slicesCost_3863 = \(slicesCost_3863);\n",
	"islicesCost_3863 = \(islicesCost_3863);\n",
	"numSlices_3920 = \(numSlices_3920);\n",
	"inumSlices_3920 = \(inumSlices_3920);\n",
	"slicesCost_3929 = \(slicesCost_3929);\n",
	"islicesCost_3929 = \(islicesCost_3929);\n",
	"numSlices_3986 = \(numSlices_3986);\n",
	"inumSlices_3986 = \(inumSlices_3986);\n",
	"slicesCost_3995 = \(slicesCost_3995);\n",
	"islicesCost_3995 = \(islicesCost_3995);\n",
	"numSlices_4052 = \(numSlices_4052);\n",
	"inumSlices_4052 = \(inumSlices_4052);\n",
	"slicesCost_4061 = \(slicesCost_4061);\n",
	"islicesCost_4061 = \(islicesCost_4061);\n",
	"numSlices_4118 = \(numSlices_4118);\n",
	"inumSlices_4118 = \(inumSlices_4118);\n",
	"slicesCost_4127 = \(slicesCost_4127);\n",
	"islicesCost_4127 = \(islicesCost_4127);\n",
	"numSlices_4184 = \(numSlices_4184);\n",
	"inumSlices_4184 = \(inumSlices_4184);\n",
	"slicesCost_4193 = \(slicesCost_4193);\n",
	"islicesCost_4193 = \(islicesCost_4193);\n",
	"constraint objective = \(objective);\n",
];

