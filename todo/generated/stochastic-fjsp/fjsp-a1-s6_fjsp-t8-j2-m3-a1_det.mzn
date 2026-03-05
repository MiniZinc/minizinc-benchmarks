int: nbTasks = 8;
int: nbJobs = 2;
int: nbMachines = 2;
set of int: TASK = 1..nbTasks;
set of int: JOB = 1..nbJobs;
set of int: MACHINE = 1..nbMachines;
set of int: ADDITIONAL_TASKS = 1..nbAdditionalTasks;
set of int: TIME = 1..maxTime;
int: maxTime = 200;
int: nbAdditionalTasks = 1;
array[TASK] of int: job = [1, 1, 1, 1, 2, 2, 2, 2];
array[TASK] of int: duration = [2, 4, 6, 1, 8, 3, 9, 3];
array[TASK] of set of int: machines_for_task = [{1, 2}, {2, 3}, {1, 3}, {1, 2, 
    3}, {2, 3}, {1, 2}, {1, 2, 3}, {1, 3}];
array[1..6, ADDITIONAL_TASKS] of int: additional_tasks_start;
array[1..6, ADDITIONAL_TASKS] of int: additional_tasks_end;
array[1..6, ADDITIONAL_TASKS] of int: additional_tasks_machine;
array[TASK] of var MACHINE: machine;
array[1..6, TASK] of var TIME: start_time;
array[1..6] of var TIME: makespan;
var 0..nbTasks*maxTime: objective;
additional_tasks_start = [| 8 | 
                            5 | 
                            11 | 
                            4 | 
                            16 | 
                            25 |];
additional_tasks_end = [| 12 | 
                          8 | 
                          18 | 
                          8 | 
                          20 | 
                          23 |];
additional_tasks_machine = [| 2 | 
                              1 | 
                              2 | 
                              1 | 
                              1 | 
                              3 |];
array[int] of int: weights = [3, 2, 1, 2, 1, 3];
constraint forall ( sc in 1..6 ) ( 
    forall ( j in JOB ) ( 
        forall ( t1, t2 in TASK where job[t1]==job[t2] /\ t1<t2 ) ( 
            start_time[sc, t1]+duration[t1]<=start_time[sc, t2] 
        ) 
    ) 
);
constraint forall ( sc in 1..6 ) ( 
    forall ( t1, t2 in TASK where t1!=t2 /\ machines_for_task[t1] intersect 
    machines_for_task[t2]!={} ) ( 
        machine[t1]==machine[t2] -> start_time[sc, t1]+duration[t1]<=start_time
    [sc, t2] \/ start_time[sc, t2]+duration[t2]<=start_time
    [sc, t1] 
    ) 
);
constraint forall ( t in TASK ) ( 
    forall ( m in MACHINE where not (m in machines_for_task[t]) ) ( 
        machine[t]!=m 
    ) 
);
constraint forall ( sc in 1..6 ) ( 
    forall ( ta in ADDITIONAL_TASKS ) ( 
        forall ( t in TASK ) ( 
            machine[t]==additional_tasks_machine[sc, ta] -> start_time[sc, t]+
    duration[t]<additional_tasks_start[sc, ta] \/ start_time[sc, t]>
    additional_tasks_end[sc, ta] 
        ) 
    ) 
);
constraint forall ( sc in 1..6 ) ( 
    forall ( t in TASK ) ( start_time[sc, t]+duration[t]<=makespan[sc] ) 
);
constraint
   objective = sum ( sc in 1..6 ) ( weights[sc]*makespan[sc] );   
solve :: seq_search([ int_search(machine, first_fail, indomain_min, complete),
                      int_search([start_time[i,j] | i in 1..6, j in TASK], first_fail, indomain_min, complete),
                      int_search(makespan, input_order, indomain_min, complete)
                   ])
	minimize objective;
output [
    "machine = ",    show(machine   ), ";\n",
    "start_time = array2d(1..6, ", show(TASK), ", ", show(start_time), ");\n",
    "makespan = ",   show(makespan  ), ";\n",
    "objective = ",  show(objective ), ";\n"
];
