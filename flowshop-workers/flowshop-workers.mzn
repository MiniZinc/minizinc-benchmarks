int: horizon;  % time horizon
set of int: Time = 0..horizon+1;
int: numberWorkers;
int: numberStations;
int: numberProducts;
int: numberProductTypes;
int: numberWorksteps = 2;

array[1..numberProducts] of int: currentStation;
array[1..numberProducts] of int: currentStep;
array[1..numberProducts] of int: currentBuffer;
array[1..numberProducts] of int: releaseTime;
array[1..numberWorkers] of int: workerInitial;
array[1..numberWorkers] of int: releaseTimeW;
array[1..numberProductTypes, 1..numberStations] of 1..2: numberManualWorksteps;
array[1..numberProductTypes, 1..numberStations] of int: setupTimes;
array[1..numberProductTypes, 1..numberStations] of int: takedownTimes;

array[1..numberStations, 1..numberStations] of int: workerMovementMatrix;
array[1..numberProductTypes, 1..numberStations] of int: productionTimeMatrix;
array[1..numberProducts] of int: productType;

int: maxd = max([productionTimeMatrix[t,m] | t in 1..numberProductTypes, m in 1..numberStations]);
int: mind = min([productionTimeMatrix[t,m] | t in 1..numberProductTypes, m in 1..numberStations]);


array[1..numberProducts, 1..numberStations, 1..numberWorksteps, 1..numberWorkers] of var opt Time : workST;
array[1..numberProducts, 1..numberStations, 1..numberWorksteps, 1..numberWorkers] of 0..maxd : workD =
  array4d(1..numberProducts, 1..numberStations, 1..numberWorksteps, 1..numberWorkers,
    [ if numberManualWorksteps[productType[product], station] == 2 then
        if workstep==1 then setupTimes[productType[product], station]
        else takedownTimes[productType[product], station] endif
      else
        if workstep==1 then productionTimeMatrix[productType[product], station]
        else 0 endif
      endif
       | product in 1..numberProducts, station in 1..numberStations,
         workstep in 1..numberWorksteps, worker in 1..numberWorkers]);

array[1..numberProducts, 1..numberStations, 1..numberWorksteps] of var opt Time : proST;
array[1..numberProducts, 1..numberStations, 1..numberWorksteps] of 0..maxd : proD =
  array3d(1..numberProducts, 1..numberStations, 1..numberWorksteps,
    [ if numberManualWorksteps[productType[product], station] == 2 then
        if workstep==1 then setupTimes[productType[product], station]
        else takedownTimes[productType[product], station] endif
      else
        if workstep==1 then productionTimeMatrix[productType[product], station]
        else 0 endif
      endif
      | product in 1..numberProducts, station in 1..numberStations, workstep in 1..numberWorksteps]);

var int: objective;

constraint objective = proST[numberProducts, numberStations, numberManualWorksteps[productType[numberProducts], numberStations]]+proD[numberProducts, numberStations, numberManualWorksteps[productType[numberProducts], numberStations]];

solve :: seq_search([
             int_search(array1d(proST), smallest, indomain_min),
             int_search([objective], input_order, indomain_min)])
      minimize objective;


% only the worksteps after the products initial station occur
constraint
forall(product in 1..numberProducts where currentStation[product] > 0)(
  ((forall(station in 1..currentStation[product]-1, workstep in 1..2)(
      absent(proST[product, station, workstep])
    )) /\
    (forall(station in currentStation[product]+1..numberStations)(
      occurs(proST[product, station, 1]) /\
      occurs(proST[product, station, 2]) == (numberManualWorksteps[productType[product], station] > 1)
    )) /\
    (absent(proST[product, currentStation[product], 1])) /\
    ((numberManualWorksteps[productType[product], currentStation[product]] == 2 /\ (currentStep[product] != 4)) -> 
       occurs(proST[product, currentStation[product], 2])) /\
    ((numberManualWorksteps[productType[product], currentStation[product]] != 2 \/ (currentStep[product] == 4)) -> 
       absent(proST[product, currentStation[product], 2]))
  ));

  
constraint
forall(product in 1..numberProducts where currentStation[product] == 0)(
  ((forall(station in 1..currentBuffer[product], workstep in 1..2)(
        absent(proST[product, station, workstep]))) /\
   (forall(station in currentBuffer[product]+1..numberStations)(
        (occurs(proST[product, station, 1])) /\
        (occurs(proST[product, station, 2]) == (numberManualWorksteps[productType[product], station] > 1)))
      )
  )
);


% symmetry breaking
constraint symmetry_breaking_constraint(forall (x in array1d(proST)) (occurs(x) <-> deopt(x)>=1));
constraint symmetry_breaking_constraint(forall (x in array1d(workST)) (occurs(x) <-> deopt(x)>=1));

% each workstep is produced by exactly one worker (so each interval is present for exactly one worker)

predicate my_alternative(var opt int: s0, var int: d0,
                         array[int] of var opt int: s,
                         array[int] of var int: d) =
          (occurs(s0) <-> exists(si in s)(occurs(si))) /\
          sum(i in index_set(s))(occurs(s[i])) <= 1 /\
          forall (i in index_set(s)) (
              occurs(s[i]) -> (deopt(s0)=deopt(s[i]) /\ deopt(s0)+d0=deopt(s[i])+d[i])
          );

% alternative constraint between product and worker "intervals"
constraint
forall(product in 1..numberProducts, station in 1..numberStations, workstep in 1..numberManualWorksteps[productType[product], station])(
    (my_alternative(proST[product, station, workstep], proD[product, station, workstep],
                    workST[product, station, workstep, 1..numberWorkers],
                    workD[product, station, workstep, 1..numberWorkers]))
);


% precedence constraints stations (a product must be processed on station1 before it can be processed on any station after station1)
constraint
forall(product in 1..numberProducts, station1 in 1..numberStations, station2 in station1+1..numberStations)(
    proD[product, station1, numberManualWorksteps[productType[product], station1]] <=
    proST[product, station2, 1] ~- proST[product, station1, numberManualWorksteps[productType[product], station1]]
);

% precedence constraints products (a station must process product1 before it can process any product in the queue after product1)
constraint
forall(product1 in 1..numberProducts, product2 in product1+1..numberProducts, station in 1..numberStations)
  (proD[product1, station, numberManualWorksteps[productType[product1], station]] <=
  proST[product2, station, 1] ~- proST[product1, station, numberManualWorksteps[productType[product1], station]]
);

% buffer constraints (at most one product can lie on a buffer)
constraint
forall(product1 in 1..numberProducts, product2 in product1+1..numberProducts, station in 1..numberStations-1)(
    proST[product1, station+1, 1] ~-
    proST[product2, station, numberManualWorksteps[productType[product2], station]] <=
    proD[product2, station, numberManualWorksteps[productType[product2], station]]
);

% automatic station (the two work steps at an automatic station must have the automatic time between them)
constraint
forall(product in 1..numberProducts, station in 1..numberStations where (numberManualWorksteps[productType[product], station] == 2))(
    (proST[product, station, 2] ~- proST[product, station, 1] ~=
    proD[product, station, 1] + productionTimeMatrix[productType[product], station]
    )
);

% if workstep1 is before workstep2, and is done by the same worker, it needs to have the walking time (for the worker) between
% using ~- here instead slows down search on the examples I tested
constraint
forall(worker in 1..numberWorkers, station in 1..numberStations, product in 1..numberProducts)(
  forall(workstep in 1..numberManualWorksteps[productType[product], station])(
    forall(station2 in 1..numberStations, product2 in 1..numberProducts)(
      forall(workstep2 in 1..numberManualWorksteps[productType[product2], station2])(
        ((product != product2 \/ station != station2 \/ workstep != workstep2) /\
        occurs(workST[product, station, workstep, worker]) /\ occurs(workST[product2, station2, workstep2, worker]) /\
        (deopt(workST[product, station, workstep, worker]) >= deopt(workST[product2, station2, workstep2, worker]))) ->
        (deopt(workST[product, station, workstep, worker]) - deopt(workST[product2, station2, workstep2, worker])) >= (workerMovementMatrix[station2, station] + workD[product2, station2, workstep2, worker])
      )
    )
  )
);


% initial positions of the workers means that no production step can start before the worker has walked to the station from its initial position
constraint
forall(worker in 1..numberWorkers, station in 1..numberStations, product in 1..numberProducts)(
  forall(workstep in 1..numberManualWorksteps[productType[product], station])(
    (workST[product, station, workstep, worker] >= workerMovementMatrix[workerInitial[worker], station] + releaseTimeW[worker])
  )
);

% product can only start being worked on after its release time
constraint
forall(product in 1..numberProducts)(
  ((currentStep[product] == 2) -> % currentStep = 2 is the setup step at an automatic station, so the automatic time has to be added to the release time
    proST[product, currentStation[product], 2] >= releaseTime[product] + productionTimeMatrix[productType[product], currentStation[product]]) /\
  ((currentStep[product] == 3) -> % currentStep = 3 is the automatic step at an automatic station, so a second step occurs at the initial station
    proST[product, currentStation[product], 2] >= releaseTime[product]) /\
  % for all other production steps after the initial station, they must start after the releasetime of the product
  forall(station in currentStation[product]+1..numberStations)(
    forall(workstep in 1..numberManualWorksteps[productType[product], station])(
      proST[product, station, workstep] >= releaseTime[product]
    )
  )
);

% if a product is still being worked on at a station, this station is "blocked" until the release time
constraint
forall(product in 1..numberProducts, product2 in product+1..numberProducts where currentStation[product] != 0)(
  proST[product2, currentStation[product], 1] >= releaseTime[product]
);
