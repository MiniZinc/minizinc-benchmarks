% Copyright 2025 Frej Knutar Lewander
% 
% Permission is hereby granted, free of charge, to any person obtaining a copy 
% of this software and associated documentation files (the “Software”), to deal 
% in the Software without restriction, including without limitation the rights 
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell 
% copies of the Software, and to permit persons to whom the Software is 
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in 
% all copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE 
% SOFTWARE.
include "globals.mzn";
int: numLocations; % the total number of locations (including the depot)
set of int: Locations = 1..numLocations;
% early[l] = the earliest visiting time of location l:
array[Locations] of int: early;
% late[l] = the latest visiting time of location l:
array[Locations] of int: late;
array[Locations, Locations] of int: duration;
int: depot = 1; % The first location is the depot
% pred[l] = the location visited before location l:
array[Locations] of var Locations: pred;
% durToPred[l] = the distance from location pred[l] to location l:
array[Locations] of var 0..max(duration): durToPred = [
    duration[l, pred[l]] | l in Locations];
% arrival[l] = the arrival at location l:
array[Locations] of var 0..max(late): arrival;
% departure[l] = the departure at location l:
array[Locations] of var min(early)..max(late): departure = [0] ++ [
    max(arrival[l], early[l]) | l in 2..numLocations];
% departurePred[l] = the departure from location pred[l]:
array[Locations] of var 0..max(late): departurePred = [
    departure[pred[l]] | l in Locations];
% The objective is the arrival back at the depot:
var int: objective = arrival[depot];
% The arrival at location l is the departure from location pred[l] + 
% The duration from pred[l] to l:
constraint forall (l in Locations) (
    arrival[l] = departurePred[l] + durToPred[l]);
% The pred variables forms a Hamiltionian circuit:
constraint circuit(pred) :: domain;
% The departure from location l is before its latest visiting time late[l]:
constraint forall (l in Locations) (departure[l] <= late[l]);
% Search strategy: first try to create the Hamiltonian circuit, then try to
%                  reduce the arrival times.
solve :: seq_search([int_search(pred, first_fail, indomain_min),
                     int_search([arrival[l] | l in arg_sort(early)],
                                input_order, indomain_min)])
         minimize objective;
