Capacitated Vehicle Routing Problem
===================================

cvrp_mip.mzn      MIP formulation

cvrp_cp.mzn       CP formulation (using the formulation from the CP
                  handbook with the giant tour representation and
                  the circuit constraint). No sym breaking constraints.

simple*.dzn       simple instances made by hand (only for testing)

A-n*-k*.dzn       A-set benchmarks (random customer locations and demand)
B-n*-k*.dzn       B-set benchmarks (clustered locations)
P-n*-k*.dzn       P-set benchmarks (modified instances from literature)

                  The A, B, and P instances come from Augerat et al [1] where
                  n is the number of customers and k is the number of vehicles.
                  The instances are also available in text format at [2].

The best known solutions for all the instances of the A, B and P sets are
available from the website at [3].



[1] Augerat, P., Belenguer, J., Benavent, E., Corbern, A.and Naddef, D., Rinaldi,
G.: Computational results with a branch and cut code for the capacitated vehicle
routing problem. Technical Report 949-M, Universite Joseph Fourier, Grenoble
(1995)

[2] http://neo.lcc.uma.es/vrp/vrp-instances/capacitated-vrp-instances/

[3] http://neo.lcc.uma.es/vrp/known-best-results/
