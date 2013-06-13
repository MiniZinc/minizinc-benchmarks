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
       buf[i, 26]  =  0
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
   (c[1, 1] = 0 /\ c[1, 2] = 0) \/ (c[1, 1] = d[1, 1] /\ c[1, 2] = d[1, 2]);
constraint
   (c[1, 4] = 0 /\ c[1, 5] = 0 /\ c[1, 6] = 0 /\ c[1, 7] = 0) \/ (c[1, 4] = d[1, 4] /\ c[1, 5] = d[1, 5] /\ c[1, 6] = d[1, 6] /\ c[1, 7] = d[1, 7]);
constraint
   (c[1, 8] = 0) \/ (c[1, 8] = d[1, 8]);
constraint
   (c[1, 9] = 0 /\ c[1, 10] = 0) \/ (c[1, 9] = d[1, 9] /\ c[1, 10] = d[1, 10]);
constraint
   (c[1, 11] = 0) \/ (c[1, 11] = d[1, 11]);
constraint
   (c[1, 13] = 0) \/ (c[1, 13] = d[1, 13]);
constraint
   (c[1, 14] = 0) \/ (c[1, 14] = d[1, 14]);
constraint
   (c[1, 16] = 0) \/ (c[1, 16] = d[1, 16]);
constraint
   (c[1, 18] = 0) \/ (c[1, 18] = d[1, 18]);
constraint
   (c[1, 19] = 0) \/ (c[1, 19] = d[1, 19]);
constraint
   (c[1, 21] = 0) \/ (c[1, 21] = d[1, 21]);
constraint
   (c[1, 23] = 0 /\ c[1, 24] = 0) \/ (c[1, 23] = d[1, 23] /\ c[1, 24] = d[1, 24]);
constraint
   (c[2, 1] = 0 /\ c[2, 2] = 0 /\ c[2, 3] = 0 /\ c[2, 4] = 0) \/ (c[2, 1] = d[2, 1] /\ c[2, 2] = d[2, 2] /\ c[2, 3] = d[2, 3] /\ c[2, 4] = d[2, 4]);
constraint
   (c[2, 6] = 0) \/ (c[2, 6] = d[2, 6]);
constraint
   (c[2, 7] = 0) \/ (c[2, 7] = d[2, 7]);
constraint
   (c[2, 8] = 0 /\ c[2, 9] = 0 /\ c[2, 10] = 0) \/ (c[2, 8] = d[2, 8] /\ c[2, 9] = d[2, 9] /\ c[2, 10] = d[2, 10]);
constraint
   (c[2, 11] = 0) \/ (c[2, 11] = d[2, 11]);
constraint
   (c[2, 12] = 0) \/ (c[2, 12] = d[2, 12]);
constraint
   (c[2, 13] = 0 /\ c[2, 14] = 0 /\ c[2, 15] = 0) \/ (c[2, 13] = d[2, 13] /\ c[2, 14] = d[2, 14] /\ c[2, 15] = d[2, 15]);
constraint
   (c[2, 16] = 0) \/ (c[2, 16] = d[2, 16]);
constraint
   (c[2, 17] = 0) \/ (c[2, 17] = d[2, 17]);
constraint
   (c[2, 18] = 0 /\ c[2, 19] = 0 /\ c[2, 20] = 0 /\ c[2, 21] = 0) \/ (c[2, 18] = d[2, 18] /\ c[2, 19] = d[2, 19] /\ c[2, 20] = d[2, 20] /\ c[2, 21] = d[2, 21]);
constraint
   (c[2, 23] = 0 /\ c[2, 24] = 0) \/ (c[2, 23] = d[2, 23] /\ c[2, 24] = d[2, 24]);
constraint
   (c[3, 1] = 0) \/ (c[3, 1] = d[3, 1]);
constraint
   (c[3, 2] = 0) \/ (c[3, 2] = d[3, 2]);
constraint
   (c[3, 4] = 0) \/ (c[3, 4] = d[3, 4]);
constraint
   (c[3, 5] = 0) \/ (c[3, 5] = d[3, 5]);
constraint
   (c[3, 6] = 0 /\ c[3, 7] = 0) \/ (c[3, 6] = d[3, 6] /\ c[3, 7] = d[3, 7]);
constraint
   (c[3, 8] = 0) \/ (c[3, 8] = d[3, 8]);
constraint
   (c[3, 10] = 0 /\ c[3, 11] = 0 /\ c[3, 12] = 0 /\ c[3, 13] = 0) \/ (c[3, 10] = d[3, 10] /\ c[3, 11] = d[3, 11] /\ c[3, 12] = d[3, 12] /\ c[3, 13] = d[3, 13]);
constraint
   (c[3, 14] = 0) \/ (c[3, 14] = d[3, 14]);
constraint
   (c[3, 16] = 0 /\ c[3, 17] = 0 /\ c[3, 18] = 0 /\ c[3, 19] = 0) \/ (c[3, 16] = d[3, 16] /\ c[3, 17] = d[3, 17] /\ c[3, 18] = d[3, 18] /\ c[3, 19] = d[3, 19]);
constraint
   (c[3, 20] = 0) \/ (c[3, 20] = d[3, 20]);
constraint
   (c[3, 21] = 0 /\ c[3, 22] = 0 /\ c[3, 23] = 0) \/ (c[3, 21] = d[3, 21] /\ c[3, 22] = d[3, 22] /\ c[3, 23] = d[3, 23]);
constraint
   (c[3, 24] = 0) \/ (c[3, 24] = d[3, 24]);
constraint
   (c[4, 2] = 0) \/ (c[4, 2] = d[4, 2]);
constraint
   (c[4, 4] = 0 /\ c[4, 5] = 0 /\ c[4, 6] = 0) \/ (c[4, 4] = d[4, 4] /\ c[4, 5] = d[4, 5] /\ c[4, 6] = d[4, 6]);
constraint
   (c[4, 7] = 0 /\ c[4, 8] = 0 /\ c[4, 9] = 0 /\ c[4, 10] = 0) \/ (c[4, 7] = d[4, 7] /\ c[4, 8] = d[4, 8] /\ c[4, 9] = d[4, 9] /\ c[4, 10] = d[4, 10]);
constraint
   (c[4, 12] = 0 /\ c[4, 13] = 0) \/ (c[4, 12] = d[4, 12] /\ c[4, 13] = d[4, 13]);
constraint
   (c[4, 14] = 0) \/ (c[4, 14] = d[4, 14]);
constraint
   (c[4, 16] = 0) \/ (c[4, 16] = d[4, 16]);
constraint
   (c[4, 18] = 0 /\ c[4, 19] = 0) \/ (c[4, 18] = d[4, 18] /\ c[4, 19] = d[4, 19]);
constraint
   (c[4, 21] = 0) \/ (c[4, 21] = d[4, 21]);
constraint
   (c[4, 22] = 0 /\ c[4, 23] = 0) \/ (c[4, 22] = d[4, 22] /\ c[4, 23] = d[4, 23]);
constraint
   (c[4, 24] = 0) \/ (c[4, 24] = d[4, 24]);
constraint
   (c[5, 2] = 0 /\ c[5, 3] = 0 /\ c[5, 4] = 0 /\ c[5, 5] = 0) \/ (c[5, 2] = d[5, 2] /\ c[5, 3] = d[5, 3] /\ c[5, 4] = d[5, 4] /\ c[5, 5] = d[5, 5]);
constraint
   (c[5, 7] = 0) \/ (c[5, 7] = d[5, 7]);
constraint
   (c[5, 8] = 0) \/ (c[5, 8] = d[5, 8]);
constraint
   (c[5, 9] = 0) \/ (c[5, 9] = d[5, 9]);
constraint
   (c[5, 11] = 0) \/ (c[5, 11] = d[5, 11]);
constraint
   (c[5, 13] = 0) \/ (c[5, 13] = d[5, 13]);
constraint
   (c[5, 14] = 0 /\ c[5, 15] = 0) \/ (c[5, 14] = d[5, 14] /\ c[5, 15] = d[5, 15]);
constraint
   (c[5, 17] = 0) \/ (c[5, 17] = d[5, 17]);
constraint
   (c[5, 19] = 0) \/ (c[5, 19] = d[5, 19]);
constraint
   (c[5, 21] = 0 /\ c[5, 22] = 0) \/ (c[5, 21] = d[5, 21] /\ c[5, 22] = d[5, 22]);
constraint
   (c[5, 24] = 0) \/ (c[5, 24] = d[5, 24]);
constraint
   (c[6, 2] = 0) \/ (c[6, 2] = d[6, 2]);
constraint
   (c[6, 4] = 0) \/ (c[6, 4] = d[6, 4]);
constraint
   (c[6, 6] = 0) \/ (c[6, 6] = d[6, 6]);
constraint
   (c[6, 8] = 0 /\ c[6, 9] = 0 /\ c[6, 10] = 0 /\ c[6, 11] = 0) \/ (c[6, 8] = d[6, 8] /\ c[6, 9] = d[6, 9] /\ c[6, 10] = d[6, 10] /\ c[6, 11] = d[6, 11]);
constraint
   (c[6, 12] = 0) \/ (c[6, 12] = d[6, 12]);
constraint
   (c[6, 13] = 0 /\ c[6, 14] = 0 /\ c[6, 15] = 0 /\ c[6, 16] = 0) \/ (c[6, 13] = d[6, 13] /\ c[6, 14] = d[6, 14] /\ c[6, 15] = d[6, 15] /\ c[6, 16] = d[6, 16]);
constraint
   (c[6, 17] = 0) \/ (c[6, 17] = d[6, 17]);
constraint
   (c[6, 18] = 0) \/ (c[6, 18] = d[6, 18]);
constraint
   (c[6, 19] = 0 /\ c[6, 20] = 0) \/ (c[6, 19] = d[6, 19] /\ c[6, 20] = d[6, 20]);
constraint
   (c[6, 21] = 0) \/ (c[6, 21] = d[6, 21]);
constraint
   (c[6, 23] = 0) \/ (c[6, 23] = d[6, 23]);
constraint
   (c[7, 2] = 0 /\ c[7, 3] = 0 /\ c[7, 4] = 0 /\ c[7, 5] = 0) \/ (c[7, 2] = d[7, 2] /\ c[7, 3] = d[7, 3] /\ c[7, 4] = d[7, 4] /\ c[7, 5] = d[7, 5]);
constraint
   (c[7, 6] = 0) \/ (c[7, 6] = d[7, 6]);
constraint
   (c[7, 8] = 0) \/ (c[7, 8] = d[7, 8]);
constraint
   (c[7, 9] = 0 /\ c[7, 10] = 0) \/ (c[7, 9] = d[7, 9] /\ c[7, 10] = d[7, 10]);
constraint
   (c[7, 11] = 0) \/ (c[7, 11] = d[7, 11]);
constraint
   (c[7, 12] = 0 /\ c[7, 13] = 0 /\ c[7, 14] = 0 /\ c[7, 15] = 0) \/ (c[7, 12] = d[7, 12] /\ c[7, 13] = d[7, 13] /\ c[7, 14] = d[7, 14] /\ c[7, 15] = d[7, 15]);
constraint
   (c[7, 16] = 0 /\ c[7, 17] = 0) \/ (c[7, 16] = d[7, 16] /\ c[7, 17] = d[7, 17]);
constraint
   (c[7, 18] = 0 /\ c[7, 19] = 0 /\ c[7, 20] = 0) \/ (c[7, 18] = d[7, 18] /\ c[7, 19] = d[7, 19] /\ c[7, 20] = d[7, 20]);
constraint
   (c[7, 22] = 0) \/ (c[7, 22] = d[7, 22]);
constraint
   (c[7, 23] = 0) \/ (c[7, 23] = d[7, 23]);
constraint
   (c[7, 24] = 0) \/ (c[7, 24] = d[7, 24]);
constraint
   (c[8, 2] = 0) \/ (c[8, 2] = d[8, 2]);
constraint
   (c[8, 3] = 0 /\ c[8, 4] = 0 /\ c[8, 5] = 0) \/ (c[8, 3] = d[8, 3] /\ c[8, 4] = d[8, 4] /\ c[8, 5] = d[8, 5]);
constraint
   (c[8, 6] = 0) \/ (c[8, 6] = d[8, 6]);
constraint
   (c[8, 8] = 0) \/ (c[8, 8] = d[8, 8]);
constraint
   (c[8, 10] = 0 /\ c[8, 11] = 0 /\ c[8, 12] = 0) \/ (c[8, 10] = d[8, 10] /\ c[8, 11] = d[8, 11] /\ c[8, 12] = d[8, 12]);
constraint
   (c[8, 13] = 0 /\ c[8, 14] = 0 /\ c[8, 15] = 0) \/ (c[8, 13] = d[8, 13] /\ c[8, 14] = d[8, 14] /\ c[8, 15] = d[8, 15]);
constraint
   (c[8, 17] = 0) \/ (c[8, 17] = d[8, 17]);
constraint
   (c[8, 19] = 0) \/ (c[8, 19] = d[8, 19]);
constraint
   (c[8, 20] = 0) \/ (c[8, 20] = d[8, 20]);
constraint
   (c[8, 21] = 0) \/ (c[8, 21] = d[8, 21]);
constraint
   (c[8, 22] = 0) \/ (c[8, 22] = d[8, 22]);
constraint
   (c[8, 24] = 0) \/ (c[8, 24] = d[8, 24]);
constraint
   (c[9, 1] = 0) \/ (c[9, 1] = d[9, 1]);
constraint
   (c[9, 3] = 0 /\ c[9, 4] = 0) \/ (c[9, 3] = d[9, 3] /\ c[9, 4] = d[9, 4]);
constraint
   (c[9, 5] = 0) \/ (c[9, 5] = d[9, 5]);
constraint
   (c[9, 6] = 0) \/ (c[9, 6] = d[9, 6]);
constraint
   (c[9, 7] = 0) \/ (c[9, 7] = d[9, 7]);
constraint
   (c[9, 8] = 0) \/ (c[9, 8] = d[9, 8]);
constraint
   (c[9, 9] = 0) \/ (c[9, 9] = d[9, 9]);
constraint
   (c[9, 10] = 0) \/ (c[9, 10] = d[9, 10]);
constraint
   (c[9, 11] = 0) \/ (c[9, 11] = d[9, 11]);
constraint
   (c[9, 12] = 0) \/ (c[9, 12] = d[9, 12]);
constraint
   (c[9, 13] = 0) \/ (c[9, 13] = d[9, 13]);
constraint
   (c[9, 14] = 0) \/ (c[9, 14] = d[9, 14]);
constraint
   (c[9, 16] = 0) \/ (c[9, 16] = d[9, 16]);
constraint
   (c[9, 17] = 0 /\ c[9, 18] = 0 /\ c[9, 19] = 0) \/ (c[9, 17] = d[9, 17] /\ c[9, 18] = d[9, 18] /\ c[9, 19] = d[9, 19]);
constraint
   (c[9, 21] = 0) \/ (c[9, 21] = d[9, 21]);
constraint
   (c[9, 23] = 0) \/ (c[9, 23] = d[9, 23]);
constraint
   (c[10, 2] = 0 /\ c[10, 3] = 0 /\ c[10, 4] = 0 /\ c[10, 5] = 0) \/ (c[10, 2] = d[10, 2] /\ c[10, 3] = d[10, 3] /\ c[10, 4] = d[10, 4] /\ c[10, 5] = d[10, 5]);
constraint
   (c[10, 6] = 0) \/ (c[10, 6] = d[10, 6]);
constraint
   (c[10, 7] = 0) \/ (c[10, 7] = d[10, 7]);
constraint
   (c[10, 9] = 0 /\ c[10, 10] = 0) \/ (c[10, 9] = d[10, 9] /\ c[10, 10] = d[10, 10]);
constraint
   (c[10, 11] = 0 /\ c[10, 12] = 0) \/ (c[10, 11] = d[10, 11] /\ c[10, 12] = d[10, 12]);
constraint
   (c[10, 14] = 0 /\ c[10, 15] = 0 /\ c[10, 16] = 0) \/ (c[10, 14] = d[10, 14] /\ c[10, 15] = d[10, 15] /\ c[10, 16] = d[10, 16]);
constraint
   (c[10, 18] = 0 /\ c[10, 19] = 0 /\ c[10, 20] = 0 /\ c[10, 21] = 0) \/ (c[10, 18] = d[10, 18] /\ c[10, 19] = d[10, 19] /\ c[10, 20] = d[10, 20] /\ c[10, 21] = d[10, 21]);
constraint
   (c[10, 22] = 0 /\ c[10, 23] = 0 /\ c[10, 24] = 0) \/ (c[10, 22] = d[10, 22] /\ c[10, 23] = d[10, 23] /\ c[10, 24] = d[10, 24]);
constraint
   (c[1, 3] = 0);
constraint
   (c[1, 12] = 0);
constraint
   (c[1, 15] = 0);
constraint
   (c[1, 17] = 0);
constraint
   (c[1, 20] = 0);
constraint
   (c[1, 22] = 0);
constraint
   (c[1, 25] = 0);
constraint
   (c[1, 26] = 0);
constraint
   (c[2, 5] = 0);
constraint
   (c[2, 22] = 0);
constraint
   (c[2, 25] = 0);
constraint
   (c[2, 26] = 0);
constraint
   (c[3, 3] = 0);
constraint
   (c[3, 9] = 0);
constraint
   (c[3, 15] = 0);
constraint
   (c[3, 25] = 0);
constraint
   (c[3, 26] = 0);
constraint
   (c[4, 1] = 0);
constraint
   (c[4, 3] = 0);
constraint
   (c[4, 11] = 0);
constraint
   (c[4, 15] = 0);
constraint
   (c[4, 17] = 0);
constraint
   (c[4, 20] = 0);
constraint
   (c[4, 25] = 0);
constraint
   (c[4, 26] = 0);
constraint
   (c[5, 1] = 0);
constraint
   (c[5, 6] = 0);
constraint
   (c[5, 10] = 0);
constraint
   (c[5, 12] = 0);
constraint
   (c[5, 16] = 0);
constraint
   (c[5, 18] = 0);
constraint
   (c[5, 20] = 0);
constraint
   (c[5, 23] = 0);
constraint
   (c[5, 25] = 0);
constraint
   (c[5, 26] = 0);
constraint
   (c[6, 1] = 0);
constraint
   (c[6, 3] = 0);
constraint
   (c[6, 5] = 0);
constraint
   (c[6, 7] = 0);
constraint
   (c[6, 22] = 0);
constraint
   (c[6, 24] = 0);
constraint
   (c[6, 25] = 0);
constraint
   (c[6, 26] = 0);
constraint
   (c[7, 1] = 0);
constraint
   (c[7, 7] = 0);
constraint
   (c[7, 21] = 0);
constraint
   (c[7, 25] = 0);
constraint
   (c[7, 26] = 0);
constraint
   (c[8, 1] = 0);
constraint
   (c[8, 7] = 0);
constraint
   (c[8, 9] = 0);
constraint
   (c[8, 16] = 0);
constraint
   (c[8, 18] = 0);
constraint
   (c[8, 23] = 0);
constraint
   (c[8, 25] = 0);
constraint
   (c[8, 26] = 0);
constraint
   (c[9, 2] = 0);
constraint
   (c[9, 15] = 0);
constraint
   (c[9, 20] = 0);
constraint
   (c[9, 22] = 0);
constraint
   (c[9, 24] = 0);
constraint
   (c[9, 25] = 0);
constraint
   (c[9, 26] = 0);
constraint
   (c[10, 1] = 0);
constraint
   (c[10, 8] = 0);
constraint
   (c[10, 13] = 0);
constraint
   (c[10, 17] = 0);
constraint
   (c[10, 25] = 0);
constraint
   (c[10, 26] = 0);

solve 
   :: int_search([buf[r,c] | r in SINDUSTRIES, c in STIMESTEPS]++[bout[r,c] | r in SINDUSTRIES, c in STIMESTEPS], largest, indomain_min, complete)
   satisfy;

output [
   "buf = ", show(buf), "\n",
   "bout = ", show(bout), "\n",
   "c = ", show(c), "\n"
];
