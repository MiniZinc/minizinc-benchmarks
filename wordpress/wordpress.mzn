% Copyright 2022 Bogdan David
% 
% Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
% 
% The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
% 
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

% Modifications by the MiniZinc Challenge Organisers:
% - Combined included files into single model file
% - Added search annotation
% - Remove unused decision variables
% - Added variable for objective

/*
 * Wordpress model for MiniZinc
 * ---------------------------------
 *
 * @author 
 *    David Bogdan
 *    bogdan.david02@e-uvt.ro
 *
 * This model was originally designed and implemented by Andrei Iovescu (andrei.iovescu99@e- uvt.ro). I only adapted it so it would have the same format as the other problems.
 */
 
/*
 * Variables for MiniZinc
 * ---------------------------------
 *
 * @b Description
 * This file is to be included in all Minizinc models.
 * It provides the definitions for the input and decision variables used in all models.
 *
 * @author 
 *    David Bogdan
 *    bogdan.david02@e-uvt.ro
 */

/***********************************
 ****                           ****
 ****      INPUT VARIABLES      ****
 ****                           ****
 ***********************************/

% Maximum number of VMs required taken from ComputeVM
int: VM;

% Number of components of the application
int: NoComponents;

% Number of hardware requirements for a component (e.g. CPU, Memory, Storage, etc.)
int: HardwareREQ;

% Requirements for each component
array[1..NoComponents, 1..HardwareREQ] of int: CompREQ;

% Number of VM Offers
int: VMOffers;

% VM specifications
array[1..VMOffers, 1..HardwareREQ] of int: VMSpecs;
array[1..VMOffers] of int: VMPrice;

% Global variable used in conflict constraints
set of int: S = { i | i in 1..NoComponents};

/***********************************
 ****                           ****
 ****     DECISION VARIABLS     ****
 ****                           ****
 ***********************************/
 
array[1..NoComponents, 1..VM] of var 0..1: AssignmentMatrix;
array[1..VM] of var 0..1: OccupancyVector;
array[1..VM] of var int: VMType;

% Data of the virtual machine on which the ith component has been deployed
% array[1..VM] of var 1..64: CPU;
% array[1..VM] of var 1700..976000: Memory;
% array[1..VM] of var 1000..24000: Storage;
array[1..VM] of var 0..16000: Price;


/*
 * Constraints for MiniZinc
 * ---------------------------------
 *
 * @b Description
 * This file is to be included in all Minizinc models.
 * It provides the definitions for the general constraints used in all models.
 *
 * @author 
 *    David Bogdan
 *    bogdan.david02@e-uvt.ro
 */

% Checks whether a specific component is deployed on at least one VM.
function var int: isDeployed(array[int, int] of var 0..1: AssignmentMatrix,
                             int: VM,
                             int: compID) =
    if(sum(k in 1..VM)(AssignmentMatrix[compID,k]) > 0) then 1 else 0 endif;
    
    
predicate deployed(array[int, int] of var 0..1: AssignmentMatrix,
                   int: VM,
                   int: compID) =
    sum(k in 1..VM)(AssignmentMatrix[compID, k]) > 0;
    
% Ensures the NULL (0) Type is reserved only for unused virtual machines
%predicate setType(array[int, int] of var 0..1: AssignmentMatrix,
%                  array[int] of var int: VMType,
%                  int: NoComponents,
%                  int: VM) =
%    forall(k in 1..VM)(
%          (sum(i in 1..NoComponents)(AssignmentMatrix[i,k])) >= 1 -> (VMType[k] > 0));   
   
                
% Ensures used VMs have their occupancy vector set
predicate occupancy(array[int, int] of var 0..1: AssignmentMatrix,
                    array[int] of var 0..1: OccupancyVector,
                    int: NoComponents,
                    int: VM) =
    forall(k in 1..VM)(
        if(sum(i in 1..NoComponents)(AssignmentMatrix[i,k]) > 0) then OccupancyVector[k] = 1 endif
    );
  
                  
% Ensures hardware requirements are met for each component
predicate capacity(array[int, int] of var 0..1: AssignmentMatrix,
                   array[int, int] of var int: CompREQ,
                   array[int, int] of var int: VMSpecs,
                   array[int] of var int: VMType,
                   int: HardwareREQ,
                   int: NoComponents,
                   int: VM) =
    forall(k in 1..VM, h in 1..HardwareREQ)  
          (sum(i in 1..NoComponents) 
          (AssignmentMatrix[i,k] * CompREQ[i,h]) <= VMSpecs[VMType[k],h]);
          
          
% Links resource arrays to VM specifications
predicate link(array[int, int] of var int: VMSpecs,
               array[int] of var int: VMPrice,
               array[int] of var 0..1: OccupancyVector,
               array[int] of var int: VMType,
               array[int] of var 0..16000: Price,
               int: VMOffers,
               int: VM) =
    forall(k in 1..VM)
          (Price[k] = VMPrice[VMType[k]] * OccupancyVector[k]);


% Ensures each component is deployed at least once
predicate basicAllocation (array[int, int] of var 0..1: AssignmentMatrix,
                           var set of int: exclusive,
                           set of int: S,
                           int: VM) 
  = forall( i in S diff exclusive)(sum (k in 1..VM) (AssignmentMatrix[i, k]) >= 1);


% Ensures unused machines have a set (default) type.
%predicate nullType(array[int, int] of var 0..1: AssignmentMatrix,
%                   array[int] of var int: VMType,
%                   int: NoComponents,
%                   int: VM) = 
%    forall(k in 1..VM)(sum(i in 1..NoComponents) 
%          
%          % If set to 0, it produces invalid index error and discards solutions which don't use all VMs
%          % If set to 1, it doesn't affect the minimal price as the price for the said VM will be 0 if it is unoccupied
%          (AssignmentMatrix[i,k]) == 0 -> VMType[k] = 1);


% Ensures a component is deployed [AT LEAST | AT MOST | EXACTLY] a set number of times
predicate lowerBound(array[int, int] of var 0..1: AssignmentMatrix,
                     int: VM,
                     int: compID, 
                     int: compID2, 
                     int: bound) =
    sum(k in 1..VM)(AssignmentMatrix[compID,k]) + sum(k in 1..VM)(AssignmentMatrix[compID2, k]) >= bound;
 
predicate lowerBound(array[int, int] of var 0..1: AssignmentMatrix,
                     int: VM,
                     int: compID,
                     int: bound) =
    sum(k in 1..VM)(AssignmentMatrix[compID,k]) >= bound;   
          
predicate upperBound(array[int, int] of var 0..1: AssignmentMatrix,
                     int: VM,
                     int: compID, 
                     int: bound) =
    sum(k in 1..VM) (AssignmentMatrix[compID, k]) <= bound;
    
predicate equalBound(array[int, int] of var 0..1: AssignmentMatrix,
                     int: VM,
                     int: compID, 
                     int: bound) =
    sum(k in 1..VM) (AssignmentMatrix[compID, k]) == bound;
   

% Ensures Provide-specific constraints         
predicate requireProvide(array[int, int] of var 0..1: AssignmentMatrix,
                         int: VM,
                         int: compID1, 
                         int: compID2, 
                         int: NoInstID1,
                         int: NoInstID2) =
    NoInstID1 * sum(k in 1..VM) (AssignmentMatrix[compID1, k]) <=
    NoInstID2 * sum(k in 1..VM) (AssignmentMatrix[compID2, k]);
    
predicate provide(array[int, int] of var 0..1: AssignmentMatrix,
                  int: VM,
                  int: compID1, 
                  int: compID2, 
                  int: NoInstID1) =
    sum(k in 1..VM) (AssignmentMatrix[compID1, k]) <=
    sum(k in 1..VM) (AssignmentMatrix[compID2, k]) * NoInstID1;

predicate boundedRequireProvide(array[int, int] of var 0..1: AssignmentMatrix,
                                int: VM,
                                int: compID1, 
                                int: compID2, 
                                int: NoInstID2) =
   (sum(k in 1..VM)(AssignmentMatrix[compID1, k]) * NoInstID2 - sum(k in 1..VM)(AssignmentMatrix[compID2,k]) > 0) /\ 
   (sum(k in 1..VM)(AssignmentMatrix[compID1, k]) * NoInstID2 - sum(k in 1..VM)(AssignmentMatrix[compID2,k])  <= NoInstID2);
     
    
% Ensures conflicting components do not share the same VM
predicate conflict(array[int, int] of var 0..1: AssignmentMatrix,
                   var set of int: conflicts,
                   int: VM,
                   int: compID) =
    forall(k in 1..VM, i in conflicts)
          (AssignmentMatrix[compID, k] + AssignmentMatrix[i, k] <= 1);
   
  
% Ensures a set component is deployed on all VMs except those containing conflicting components
predicate fullDeployment(array[int, int] of var 0..1: AssignmentMatrix,
                         var set of int: conflicts,
                         int: VM,
                         int: NoComponents,
                         int: compID) =
         forall(k in 1..VM)(
             if(sum(i in conflicts)(AssignmentMatrix[i,k]) == 0 /\ sum(i in 1..NoComponents)(AssignmentMatrix[i,k]) != 0) then AssignmentMatrix[compID,k] = 1 endif
         );

% Ensures components in a given set are placed on the same VM
predicate colocation(array[int, int] of var 0..1: AssignmentMatrix,
                     var set of int: components,
                     int: VM) =
        forall(k in 1..VM)(
            forall(i in components, j in components)(
                AssignmentMatrix[i,k] = AssignmentMatrix[j,k]
            )
        );

% Ensures that two components are not deployed simultaneously
predicate exclusiveDeployment(array[int, int] of var 0..1: AssignmentMatrix,
                              int: VM,
                              int: CompID1,
                              int: CompID2) =
        sum(k in 1..VM)(AssignmentMatrix[CompID1, k]) > 0 xor sum(k in 1..VM)(AssignmentMatrix[CompID2, k]) > 0;

/***********************************
 ****                           ****
 ****      INPUT VARIABLES      ****
 ****                           ****
 ***********************************/
int: WPInstances;

/***********************************
 ****                           ****
 ****        CONSTANTS          ****
 ****                           ****
 ***********************************/
int: Wordpress = 1;
int: MySQL = 2;
int: DNS_LoadBalancer = 3;
int: HTTP_LoadBalancer = 4;
int: Varnish = 5;

/***********************************
 ****                           ****
 ****      MODELING PROBLEM     ****
 ****                           ****
 ***********************************/
constraint basicAllocation(AssignmentMatrix, {DNS_LoadBalancer, HTTP_LoadBalancer}, S, VM);
constraint occupancy(AssignmentMatrix, OccupancyVector, NoComponents, VM);
constraint capacity(AssignmentMatrix, CompREQ, VMSpecs, VMType, HardwareREQ, NoComponents, VM);
constraint link(VMSpecs, VMPrice, OccupancyVector, VMType, Price, VMOffers, VM);

% Problem specific constraints
constraint exclusiveDeployment(AssignmentMatrix, VM, DNS_LoadBalancer, HTTP_LoadBalancer);

constraint if(isDeployed(AssignmentMatrix, VM, DNS_LoadBalancer) == 1)
then 
    requireProvide(AssignmentMatrix, VM, Wordpress, DNS_LoadBalancer, 1, 7)
else
    requireProvide(AssignmentMatrix, VM, Wordpress, HTTP_LoadBalancer, 1, 3)
endif;

constraint requireProvide(AssignmentMatrix, VM, Wordpress, MySQL, 2, 3);

constraint conflict(AssignmentMatrix, {DNS_LoadBalancer, HTTP_LoadBalancer, MySQL}, VM, Varnish);
constraint conflict(AssignmentMatrix, {Wordpress, MySQL, Varnish}, VM, DNS_LoadBalancer);
constraint conflict(AssignmentMatrix, {Wordpress, MySQL, Varnish}, VM, HTTP_LoadBalancer);

constraint lowerBound(AssignmentMatrix, VM, Wordpress, WPInstances);
constraint lowerBound(AssignmentMatrix, VM, Varnish, 2);
constraint lowerBound(AssignmentMatrix, VM, MySQL, 2);
constraint upperBound(AssignmentMatrix, VM, DNS_LoadBalancer, 1);


/***********************************
 ****                           ****
 ****      SOLVING PROBLEM      ****
 ****                           ****
 ***********************************/
var int: objective = sum(k in 1..VM)(Price[k]);
solve :: int_search(
  array1d(AssignmentMatrix) ++
  OccupancyVector ++
  VMType ++
  Price,
  first_fail,
  indomain_min
) minimize objective;
