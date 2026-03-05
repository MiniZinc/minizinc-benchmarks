include "globals.mzn";
enum TOWER;

enum HANDSET;

int: min_signal_strength;

int: maxpower = 10;
set of int: POWER = 1..maxpower;
array [POWER] of int: effective_power = [ 2 * (p-1) * (p-1) | p in POWER ];

array [TOWER] of int: capacity;
array [HANDSET] of int: demand;

% main decisions
array[TOWER] of var 0..maxpower: power;

float: POWER_SCALE = 10000;
array[HANDSET, TOWER] of float: distance;

% Effective power loss for handset/tower pairs. Scaled up to make everything integer.
array[HANDSET, TOWER] of float: attenuation = array2d(HANDSET,TOWER,
  [ POWER_SCALE / (distance[h, t] * distance[h, t]) | h in HANDSET, t in TOWER ]);
array[HANDSET, TOWER] of int: attenuation_i = array2d(HANDSET, TOWER, [round(attenuation[h, t]) | h in HANDSET, t in TOWER ]);
%constraint trace("attenuation = \(attenuation);\n");

array[HANDSET] of var TOWER: tower = [ to_enum(TOWER, arg_max(t in TOWER)(signal_strength(t, h))) | h in HANDSET ];

% Manual implementation of Boolean par argmax.
function int: arg_max_(array [int] of int: idx, array [int] of int: tl, int: best, int: acc) =
  if length(tl) = 0 then
    best
  elseif tl[1] > acc then
    arg_max_(array1d(idx[2..]), array1d(tl[2..]), idx[1], tl[1])
  else
    arg_max_(array1d(idx[2..]), array1d(tl[2..]), best, acc)
  endif;

function int: arg_max(array [int] of bool: elts) =
  let {
    array [int] of int: idx = [i | i in index_set(elts)] ;
    array [int] of int: vals = [ bool2int(b) | b in elts ] ;
  } in
  arg_max_(array1d(idx[2..]), array1d(vals[2..]), idx[1], vals[1]);

var int: signal_strength(var TOWER: t, HANDSET: h) = 
                         attenuation_i[h, t] * effective_power[power[t]];

% What is the minimum strength for t to transmit to h?
% Computed as the real minimum value.
function int: min_transmit_power(TOWER: t, HANDSET: h) ::promise_total =
  let {
    array [int] of bool: sel =
      [effective_power[p] * attenuation[h, t] >= min_signal_strength | p in POWER]
      ++ [true] ;
  } in
  arg_max(sel);

% minium signal strength                         
constraint forall (h in HANDSET) ([ power[t] >= min_transmit_power(t, h) | t in TOWER ][tower[h]]);
% constraint forall(h in HANDSET)(signal_strength(tower[h], h) >= min_signal_strength);
                                                                        
% max handsets
include "global_cardinality_low_up.mzn";
array [TOWER] of var bool: overloaded = [ sum (h in HANDSET) (demand[h] * (tower[h] == t)) > capacity[t] | t in TOWER ];

% non interference
% array[HANDSET] of var int: connection_quality =
  % [ 1000*signal_strength(tower[h],h) div sum(t in TOWER)(signal_strength(t,h)) | h in HANDSET ];

array[HANDSET] of var int: connection_quality = [not overloaded[tower[h]] | h in HANDSET];
var int: objective = sum(connection_quality);


solve ::seq_search([
  int_search(tower, first_fail, indomain_min),
  int_search(power, first_fail, indomain_min)
  ]) maximize objective;
