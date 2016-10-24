Capacitated Vehicle Routing Problem
===================================

Note that we already have this problem (with the same instances) in the MiniZinc 
benchmark suite ('vrp'), however that is a MIP model.

cvrp.mzn		  CP formulation (using the formulation from the CP
                          handbook with the giant tour representation and 
                          the circuit constraint). No sym breaking constraints.

simple*.dzn		  simple instances made by hand (only for testing)  

A-n*.dzn                  A-set benchmarks (random customer locations and demand)
B-n*.dzn                  B-set benchmarks (clustered locations)
P-n*.dzn 		  P-set benchmarks (modified instances from literature)

			  The A,B,P benchmarks come from Augerat et al [1] where 
                          n is the number of customers. They are also available
                          in text format at [2].

best_known_solutions.txt  The best known solutions for all the instances of the 
                          A,B and P set, as obtained from the website at [3]



[1] Augerat, P., Belenguer, J., Benavent, E., Corbern, A.and Naddef, D., Rinaldi,
G.: Computational results with a branch and cut code for the capacitated vehicle
routing problem. Technical Report 949-M, Universite Joseph Fourier, Grenoble
(1995)

[2] http://neo.lcc.uma.es/vrp/vrp-instances/capacitated-vrp-instances/

[3] http://neo.lcc.uma.es/vrp/known-best-results/
