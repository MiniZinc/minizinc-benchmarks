% input parameters

int: reference_makespan;
int: reference_waste;
int: reference_tardiness;


int: program_setup_time;
int: sequence_setup_time;

int: additional_setup_time = program_setup_time - sequence_setup_time;

int: max_colors_per_job;
int: max_moulds_per_job = max(slots_per_program);

int: min_cycles_per_job;
int: max_cycles_per_job;
int: max_jobs;
set of int: jobs = 1..max_jobs;

int: num_colors;
set of int: colors = 1..num_colors;

int: num_programs;
set of int: programs = 1..num_programs;

int: num_moulds;
set of int: moulds = 1..num_moulds;

int: num_demands;
set of int: demands = 1..num_demands;

int: num_lines;
set of int: lines = 1..num_lines;

array[moulds] of int: available_moulds;
array[moulds] of set of int: demanded_colors_for_mould = [
                                                  {c | c in colors where
                                                    exists(d in demands)(demand_color[d] = c
                                                                         /\ demand_mould[d] = m)                                         
                                                  }
                                                | m in moulds];

array[programs] of int: slots_per_program;
array[0..num_programs] of int: slots_per_program_0 = array1d(0..num_programs, [0] ++ slots_per_program);

array[programs] of int: cycle_time_for_program;
array[0..num_programs] of int: cycle_time_for_program_0 = array1d(0..num_programs, [0] ++ cycle_time_for_program);

array[moulds] of programs: program_for_mould;
array[moulds] of lines: line_for_mould;

array[colors, colors] of 0..1: color_compatibility;

array[demands] of int: demand_qty;
array[demands] of int: demand_duedate;
array[demands] of colors: demand_color;
array[demands] of moulds: demand_mould;

array[demands] of set of int: compatible_demands = [
                                                    {d2 | d2 in demands where  demand_duedate[d2] <= demand_duedate[d]
                                                                               /\ demand_mould[d2] = demand_mould[d]
                                                                               /\ demand_color[d2] = demand_color[d]
                                                    }
                                                    | d in demands];

% decision variables
array[jobs] of var 0..num_programs: job_program;
set of int: cycle_set = min_cycles_per_job..max_cycles_per_job;
array[jobs] of var cycle_set: job_length;
array[jobs, moulds, colors] of var 0..max_moulds_per_job: job_moulds;
array[jobs, moulds, colors] of var 0..max_moulds_per_job*max_cycles_per_job: total_job_moulds;

% constraints

% break symmetries
constraint forall(i in 1..max_jobs-1)(
  (job_program[i] = 0) -> (job_program[i+1] = 0)
);
constraint forall(i in jobs)(
  ((job_program[i] = 0) -> (job_length[i] = min_cycles_per_job))
);

% check number of assigned moulds per job
constraint forall(i in jobs)(
  sum(k in moulds, l in colors)(job_moulds[i,k,l]) = slots_per_program_0[job_program[i]]
);

% check number of available moulds per type
constraint forall(i in jobs, k in moulds)(
  sum(l in colors)(job_moulds[i,k,l]) <= available_moulds[k]
);

% check the number of colors and lines per job
constraint forall(i in jobs)(
  count(l in colors, m in lines)(sum(k in moulds where line_for_mould[k] = m)(job_moulds[i,k,l]) > 0) <= max_colors_per_job
);

% check demands are fulfilled
constraint forall(m in moulds, c in demanded_colors_for_mould[m])(
  sum(d in demands where demand_mould[d] = m /\ demand_color[d] = c)(demand_qty[d])
  <=
  sum(i in jobs) (total_job_moulds[i,m,c])
);

% enforce that moulds are compatible with programs
constraint forall(i in jobs, k in moulds)(
  (job_program[i] != program_for_mould[k]) -> forall(l in colors)(job_moulds[i,k,l] = 0)
);

% check color compatiblity
constraint forall(i in jobs, c1 in colors, c2 in c1+1..num_colors where color_compatibility[c1,c2] = 0)(
  (sum(k in moulds)(job_moulds[i,k,c1]) > 0)
  -> (forall(k in moulds)(job_moulds[i,k,c2] = 0))
);

% channel total job moulds
constraint forall(i in jobs, k in moulds, l in colors)(
  total_job_moulds[i,k,l] = job_moulds[i,k,l] * job_length[i]
);


% soft constraints
%
% auxiliary variables
%
int: max_cycle_time = max(cycle_time_for_program);
int: min_cycle_time = min(cycle_time_for_program);
int: lower_bound_end = min_cycle_time*min_cycles_per_job;
int: upper_bound_end = max_jobs*max_cycles_per_job*max_cycle_time
                        + max_jobs*program_setup_time;
int: upper_bound_time = max_cycles_per_job*max_cycle_time;

int: ub_waste_per_job = max_moulds_per_job*max_cycles_per_job;

array[jobs] of var lower_bound_end..upper_bound_end: job_end;
array[jobs] of var 0..upper_bound_time: job_time;
array[demands] of var lower_bound_end..upper_bound_end: demand_end;
array[demands] of var jobs: demand_end_job;

var lower_bound_end..upper_bound_end: makespan;
var 0..ub_waste_per_job*max_jobs: waste;
int: ub_tardiness = sum(d in demands)(max([0,upper_bound_end-demand_duedate[d]]));
var 0..ub_tardiness: tardiness;

%
% soft constraints
%

% set job times
constraint forall(i in jobs, p in programs where job_program[i] == p)(
  job_time[i] = job_length[i]*cycle_time_for_program_0[p]
);


% set job end times
constraint forall(i in jobs where job_program[i] > 0)(
  job_end[i] = job_time[1] + sum(k in 2..i)(job_time[k] + sequence_setup_time
                 + bool2int(job_program[k-1] != job_program[k])
                 * additional_setup_time)
);
constraint forall(i in jobs where job_program[i] = 0)(
  job_end[i] = lower_bound_end
);


% set demand end times
constraint forall(d in demands)(
let {
   int: k = demand_mould[d];
   int: l = demand_color[d];  
}
in
  demand_end[d] = job_end[demand_end_job[d]]
  /\
  job_program[demand_end_job[d]] > 0
  /\
  sum(i in 1..demand_end_job[d]) (total_job_moulds[i,k,l])
  >= sum(d2 in compatible_demands[d])
     (demand_qty[d2])
  /\
  sum(i in 1..demand_end_job[d]-1) (total_job_moulds[i,k,l])
  < sum(d2 in compatible_demands[d])
     (demand_qty[d2])  
);

% makespan
constraint (
  makespan = max(job_end)
);

% waste
constraint (
  waste = sum(i in jobs,
              k in moulds,
              l in colors)(total_job_moulds[i,k,l])
          - 
          sum(d in demands)(demand_qty[d])
);

% tardiness
constraint (
   tardiness = sum(d in demands)(max([0,demand_end[d] - demand_duedate[d]]))
);

ann : search = int_search([job_moulds[i,k,l] | i in jobs, k in moulds, l in colors],
                          smallest,
                          indomain_min,
                          complete);
solve::search minimize makespan + tardiness + waste;
