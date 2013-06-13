% Miquel Bofill <mbofill@ima.udg.edu>
% 
% Waste Water Treatment Plant Scheduling Problem

int: INDUSTRIES;
int: TIMESTEPS;
int: max_capacitat;
set of int: SINDUSTRIES = 1..INDUSTRIES;
set of int: STIMESTEPS = 1..TIMESTEPS;
array [SINDUSTRIES, STIMESTEPS] of var int: buf;
array [SINDUSTRIES, STIMESTEPS] of var int: bout;
array [SINDUSTRIES, STIMESTEPS] of var int: c;
array [SINDUSTRIES] of int: TankFlow;
array [SINDUSTRIES] of int: TankCapacity;
array [SINDUSTRIES, STIMESTEPS] of var int: d;

constraint
   forall ( j in STIMESTEPS ) (
       sum( i in SINDUSTRIES) ( c[i, j] + bout[i, j] ) <= max_capacitat
   );
constraint
   forall ( i in SINDUSTRIES ) (
       buf[i, 1]  =  d[i, 1] - c[i, 1]
   );
constraint
   forall ( i in SINDUSTRIES ) (
       buf[i, 24]  =  0
   );
constraint
   forall ( i in SINDUSTRIES, j in 2..TIMESTEPS ) (
       buf[i, j]  =  buf[i, j-1] - bout[i, j] + d[i, j] - c[i, j]
   );
constraint
   forall ( i in SINDUSTRIES, j in STIMESTEPS ) (
       buf[i, j]  >=  0
   );
constraint
   forall ( i in SINDUSTRIES, j in STIMESTEPS ) (
       bout[i, j]  >=  0
   );
constraint
   forall ( i in SINDUSTRIES, j in STIMESTEPS ) (
       bout[i, j]  <=  TankFlow[i]
   );
constraint
   forall ( i in SINDUSTRIES, j in STIMESTEPS ) (
       buf[i, j]  <=  TankCapacity[i]
   );
constraint
   forall ( i in SINDUSTRIES, j in 2..TIMESTEPS ) (
       bout[i, j]  <=  buf[i, j-1]
   );
constraint
   forall ( i in SINDUSTRIES ) (
       bout[i, 1]  =  0
   );
constraint
   forall ( i in SINDUSTRIES, j in 2..TIMESTEPS ) (
       (bout[i, j]  =  0) \/ (bout[i, j]=TankFlow[i] /\ buf[i, j-1] > TankFlow[i]) \/ (bout[i, j] = buf[i, j-1] /\ buf[i, j-1] <= TankFlow[i])
   );
constraint
   (c[1, 3] = 0) \/ (c[1, 3] = d[1, 3]);
constraint
   (c[1, 5] = 0) \/ (c[1, 5] = d[1, 5]);
constraint
   (c[1, 7] = 0) \/ (c[1, 7] = d[1, 7]);
constraint
   (c[1, 9] = 0) \/ (c[1, 9] = d[1, 9]);
constraint
   (c[1, 11] = 0) \/ (c[1, 11] = d[1, 11]);
constraint
   (c[1, 13] = 0) \/ (c[1, 13] = d[1, 13]);
constraint
   (c[1, 15] = 0) \/ (c[1, 15] = d[1, 15]);
constraint
   (c[1, 17] = 0) \/ (c[1, 17] = d[1, 17]);
constraint
   (c[1, 19] = 0) \/ (c[1, 19] = d[1, 19]);
constraint
   (c[1, 21] = 0) \/ (c[1, 21] = d[1, 21]);
constraint
   (c[1, 23] = 0) \/ (c[1, 23] = d[1, 23]);
constraint
   (c[2, 13] = 0) \/ (c[2, 13] = d[2, 13]);
constraint
   (c[3, 4] = 0 /\ c[3, 5] = 0) \/ (c[3, 4] = d[3, 4] /\ c[3, 5] = d[3, 5]);
constraint
   (c[3, 10] = 0) \/ (c[3, 10] = d[3, 10]);
constraint
   (c[3, 14] = 0 /\ c[3, 15] = 0 /\ c[3, 16] = 0) \/ (c[3, 14] = d[3, 14] /\ c[3, 15] = d[3, 15] /\ c[3, 16] = d[3, 16]);
constraint
   (c[3, 21] = 0) \/ (c[3, 21] = d[3, 21]);
constraint
   (c[4, 1] = 0) \/ (c[4, 1] = d[4, 1]);
constraint
   (c[4, 2] = 0) \/ (c[4, 2] = d[4, 2]);
constraint
   (c[4, 3] = 0) \/ (c[4, 3] = d[4, 3]);
constraint
   (c[4, 4] = 0) \/ (c[4, 4] = d[4, 4]);
constraint
   (c[4, 5] = 0) \/ (c[4, 5] = d[4, 5]);
constraint
   (c[4, 6] = 0) \/ (c[4, 6] = d[4, 6]);
constraint
   (c[4, 7] = 0) \/ (c[4, 7] = d[4, 7]);
constraint
   (c[4, 8] = 0) \/ (c[4, 8] = d[4, 8]);
constraint
   (c[4, 9] = 0) \/ (c[4, 9] = d[4, 9]);
constraint
   (c[4, 10] = 0) \/ (c[4, 10] = d[4, 10]);
constraint
   (c[4, 11] = 0) \/ (c[4, 11] = d[4, 11]);
constraint
   (c[4, 12] = 0) \/ (c[4, 12] = d[4, 12]);
constraint
   (c[4, 13] = 0) \/ (c[4, 13] = d[4, 13]);
constraint
   (c[4, 14] = 0) \/ (c[4, 14] = d[4, 14]);
constraint
   (c[4, 15] = 0) \/ (c[4, 15] = d[4, 15]);
constraint
   (c[4, 16] = 0) \/ (c[4, 16] = d[4, 16]);
constraint
   (c[4, 17] = 0) \/ (c[4, 17] = d[4, 17]);
constraint
   (c[4, 18] = 0) \/ (c[4, 18] = d[4, 18]);
constraint
   (c[4, 19] = 0) \/ (c[4, 19] = d[4, 19]);
constraint
   (c[4, 20] = 0) \/ (c[4, 20] = d[4, 20]);
constraint
   (c[4, 21] = 0) \/ (c[4, 21] = d[4, 21]);
constraint
   (c[4, 22] = 0) \/ (c[4, 22] = d[4, 22]);
constraint
   (c[4, 23] = 0) \/ (c[4, 23] = d[4, 23]);
constraint
   (c[4, 24] = 0) \/ (c[4, 24] = d[4, 24]);
constraint
   (c[5, 6] = 0) \/ (c[5, 6] = d[5, 6]);
constraint
   (c[5, 16] = 0) \/ (c[5, 16] = d[5, 16]);
constraint
   (c[6, 2] = 0 /\ c[6, 3] = 0) \/ (c[6, 2] = d[6, 2] /\ c[6, 3] = d[6, 3]);
constraint
   (c[6, 8] = 0 /\ c[6, 9] = 0 /\ c[6, 10] = 0) \/ (c[6, 8] = d[6, 8] /\ c[6, 9] = d[6, 9] /\ c[6, 10] = d[6, 10]);
constraint
   (c[6, 13] = 0) \/ (c[6, 13] = d[6, 13]);
constraint
   (c[6, 16] = 0) \/ (c[6, 16] = d[6, 16]);
constraint
   (c[6, 21] = 0 /\ c[6, 22] = 0) \/ (c[6, 21] = d[6, 21] /\ c[6, 22] = d[6, 22]);
constraint
   (c[7, 1] = 0) \/ (c[7, 1] = d[7, 1]);
constraint
   (c[7, 2] = 0) \/ (c[7, 2] = d[7, 2]);
constraint
   (c[7, 3] = 0) \/ (c[7, 3] = d[7, 3]);
constraint
   (c[7, 4] = 0) \/ (c[7, 4] = d[7, 4]);
constraint
   (c[7, 5] = 0) \/ (c[7, 5] = d[7, 5]);
constraint
   (c[7, 6] = 0) \/ (c[7, 6] = d[7, 6]);
constraint
   (c[7, 7] = 0) \/ (c[7, 7] = d[7, 7]);
constraint
   (c[7, 8] = 0) \/ (c[7, 8] = d[7, 8]);
constraint
   (c[7, 9] = 0) \/ (c[7, 9] = d[7, 9]);
constraint
   (c[7, 10] = 0) \/ (c[7, 10] = d[7, 10]);
constraint
   (c[7, 11] = 0) \/ (c[7, 11] = d[7, 11]);
constraint
   (c[7, 12] = 0) \/ (c[7, 12] = d[7, 12]);
constraint
   (c[7, 13] = 0) \/ (c[7, 13] = d[7, 13]);
constraint
   (c[7, 14] = 0) \/ (c[7, 14] = d[7, 14]);
constraint
   (c[7, 15] = 0) \/ (c[7, 15] = d[7, 15]);
constraint
   (c[7, 16] = 0) \/ (c[7, 16] = d[7, 16]);
constraint
   (c[7, 17] = 0) \/ (c[7, 17] = d[7, 17]);
constraint
   (c[7, 18] = 0) \/ (c[7, 18] = d[7, 18]);
constraint
   (c[7, 19] = 0) \/ (c[7, 19] = d[7, 19]);
constraint
   (c[7, 20] = 0) \/ (c[7, 20] = d[7, 20]);
constraint
   (c[7, 21] = 0) \/ (c[7, 21] = d[7, 21]);
constraint
   (c[7, 22] = 0) \/ (c[7, 22] = d[7, 22]);
constraint
   (c[7, 23] = 0) \/ (c[7, 23] = d[7, 23]);
constraint
   (c[8, 3] = 0) \/ (c[8, 3] = d[8, 3]);
constraint
   (c[8, 5] = 0) \/ (c[8, 5] = d[8, 5]);
constraint
   (c[8, 7] = 0) \/ (c[8, 7] = d[8, 7]);
constraint
   (c[8, 9] = 0) \/ (c[8, 9] = d[8, 9]);
constraint
   (c[8, 11] = 0) \/ (c[8, 11] = d[8, 11]);
constraint
   (c[8, 15] = 0) \/ (c[8, 15] = d[8, 15]);
constraint
   (c[8, 16] = 0) \/ (c[8, 16] = d[8, 16]);
constraint
   (c[8, 17] = 0) \/ (c[8, 17] = d[8, 17]);
constraint
   (c[8, 18] = 0) \/ (c[8, 18] = d[8, 18]);
constraint
   (c[8, 19] = 0) \/ (c[8, 19] = d[8, 19]);
constraint
   (c[8, 20] = 0) \/ (c[8, 20] = d[8, 20]);
constraint
   (c[8, 21] = 0) \/ (c[8, 21] = d[8, 21]);
constraint
   (c[8, 22] = 0) \/ (c[8, 22] = d[8, 22]);
constraint
   (c[8, 23] = 0) \/ (c[8, 23] = d[8, 23]);
constraint
   (c[8, 24] = 0) \/ (c[8, 24] = d[8, 24]);
constraint
   (c[1, 1] = 0);
constraint
   (c[1, 2] = 0);
constraint
   (c[1, 4] = 0);
constraint
   (c[1, 6] = 0);
constraint
   (c[1, 8] = 0);
constraint
   (c[1, 10] = 0);
constraint
   (c[1, 12] = 0);
constraint
   (c[1, 14] = 0);
constraint
   (c[1, 16] = 0);
constraint
   (c[1, 18] = 0);
constraint
   (c[1, 20] = 0);
constraint
   (c[1, 22] = 0);
constraint
   (c[1, 24] = 0);
constraint
   (c[2, 1] = 0);
constraint
   (c[2, 2] = 0);
constraint
   (c[2, 3] = 0);
constraint
   (c[2, 4] = 0);
constraint
   (c[2, 5] = 0);
constraint
   (c[2, 6] = 0);
constraint
   (c[2, 7] = 0);
constraint
   (c[2, 8] = 0);
constraint
   (c[2, 9] = 0);
constraint
   (c[2, 10] = 0);
constraint
   (c[2, 11] = 0);
constraint
   (c[2, 12] = 0);
constraint
   (c[2, 14] = 0);
constraint
   (c[2, 15] = 0);
constraint
   (c[2, 16] = 0);
constraint
   (c[2, 17] = 0);
constraint
   (c[2, 18] = 0);
constraint
   (c[2, 19] = 0);
constraint
   (c[2, 20] = 0);
constraint
   (c[2, 21] = 0);
constraint
   (c[2, 22] = 0);
constraint
   (c[2, 23] = 0);
constraint
   (c[2, 24] = 0);
constraint
   (c[3, 1] = 0);
constraint
   (c[3, 2] = 0);
constraint
   (c[3, 3] = 0);
constraint
   (c[3, 6] = 0);
constraint
   (c[3, 7] = 0);
constraint
   (c[3, 8] = 0);
constraint
   (c[3, 9] = 0);
constraint
   (c[3, 11] = 0);
constraint
   (c[3, 12] = 0);
constraint
   (c[3, 13] = 0);
constraint
   (c[3, 17] = 0);
constraint
   (c[3, 18] = 0);
constraint
   (c[3, 19] = 0);
constraint
   (c[3, 20] = 0);
constraint
   (c[3, 22] = 0);
constraint
   (c[3, 23] = 0);
constraint
   (c[3, 24] = 0);
constraint
   (c[5, 1] = 0);
constraint
   (c[5, 2] = 0);
constraint
   (c[5, 3] = 0);
constraint
   (c[5, 4] = 0);
constraint
   (c[5, 5] = 0);
constraint
   (c[5, 7] = 0);
constraint
   (c[5, 8] = 0);
constraint
   (c[5, 9] = 0);
constraint
   (c[5, 10] = 0);
constraint
   (c[5, 11] = 0);
constraint
   (c[5, 12] = 0);
constraint
   (c[5, 13] = 0);
constraint
   (c[5, 14] = 0);
constraint
   (c[5, 15] = 0);
constraint
   (c[5, 17] = 0);
constraint
   (c[5, 18] = 0);
constraint
   (c[5, 19] = 0);
constraint
   (c[5, 20] = 0);
constraint
   (c[5, 21] = 0);
constraint
   (c[5, 22] = 0);
constraint
   (c[5, 23] = 0);
constraint
   (c[5, 24] = 0);
constraint
   (c[6, 1] = 0);
constraint
   (c[6, 4] = 0);
constraint
   (c[6, 5] = 0);
constraint
   (c[6, 6] = 0);
constraint
   (c[6, 7] = 0);
constraint
   (c[6, 11] = 0);
constraint
   (c[6, 12] = 0);
constraint
   (c[6, 14] = 0);
constraint
   (c[6, 15] = 0);
constraint
   (c[6, 17] = 0);
constraint
   (c[6, 18] = 0);
constraint
   (c[6, 19] = 0);
constraint
   (c[6, 20] = 0);
constraint
   (c[6, 23] = 0);
constraint
   (c[6, 24] = 0);
constraint
   (c[7, 24] = 0);
constraint
   (c[8, 1] = 0);
constraint
   (c[8, 2] = 0);
constraint
   (c[8, 4] = 0);
constraint
   (c[8, 6] = 0);
constraint
   (c[8, 8] = 0);
constraint
   (c[8, 10] = 0);
constraint
   (c[8, 12] = 0);
constraint
   (c[8, 13] = 0);
constraint
   (c[8, 14] = 0);

solve 
   :: int_search([buf[r,c] | r in SINDUSTRIES, c in STIMESTEPS]++[bout[r,c] | r in SINDUSTRIES, c in STIMESTEPS], largest, indomain_min, complete)
   satisfy;

output [
   "buf = ", show(buf), "\n",
   "bout = ", show(bout), "\n",
   "c = ", show(c), "\n"
];
