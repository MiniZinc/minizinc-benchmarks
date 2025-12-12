%%% Frontlader CONFIGURATION


% The MIT License (MIT)
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in
% all copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
% THE SOFTWARE.

% Number of capacitated vehicles and customers
int: num_vehicles;
int: num_customers;
int: total_places = num_customers + 1; % Includes the depot

% Distance matrix for depot and customers
array[1..total_places, 1..total_places] of int: predicted_ETAs;

% Decision variables for vehicle visits and order of visits
array[1..num_vehicles, 1..total_places] of var 0..1: visit;
array[1..num_vehicles, 1..total_places+1] of var 0..total_places+1: order; % +1 to accommodate an explicit index for the vehicle's return to the depot

% Capacities of the vehicles
array[1..num_vehicles] of int: vehicle_capacities;

% Predicted demands at each customer
array[1..total_places] of int: predicted_demands;

% Capacity constraint: Each vehicle's total load does not exceed its capacity
constraint forall(v in 1..num_vehicles) (
    sum(c in 1..total_places)(predicted_demands[c] * visit[v, c]) <= vehicle_capacities[v]
);

% Constraint to ensure each customer location is visited exactly once by one vehicle
constraint forall(c in 2..total_places) (
    sum(v in 1..num_vehicles)(visit[v, c]) = 1
);

% Depot start constraint
constraint forall(v in 1..num_vehicles) (
    visit[v, 1] = 1 /\ order[v, 1] = 1
);

% Sequential order for visited locations (tour allocation)
constraint forall(v in 1..num_vehicles, c in 2..total_places) (
    if visit[v, c] = 1 then
        order[v, c] > max([order[v, k] | k in 1..c-1 where visit[v, k] = 1])
    else
        order[v, c] = 0
    endif
);

% Enforce return to depot
constraint forall(v in 1..num_vehicles) (
    let {
        var int: last_customer_order = max([order[v, c] | c in 2..total_places where visit[v, c] = 1])
    } in (
        visit[v, 1] = 1 /\ order[v, total_places+1] = last_customer_order + 1
    )
);

% Calculate the total ETA, including the return to the depot
var int: total_ETA = sum(v in 1..num_vehicles)(
    sum(i in 1..total_places-1)(
        sum(j in i+1..total_places)(
            if visit[v, i] = 1 /\ visit[v, j] = 1 then
                predicted_ETAs[i, j]
            else
                0
            endif
        )
    ) +
    % Calculate ETA from the last customer to the depot
    let {
        var int: last_customer = max([c | c in 2..total_places where visit[v, c] = 1])
    } in (
        if visit[v, last_customer] = 1 then
            predicted_ETAs[last_customer, 1]
        else
            0
        endif
    )
);

% Objective function to minimize distance
solve :: int_search([order[v, c] | v in 1..num_vehicles, c in 1..total_places+1], first_fail, indomain_min, complete) minimize total_ETA;
