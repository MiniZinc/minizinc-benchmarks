%==============================================================================
%
% A optimization variant of the minimal disagreement parity (MDP) problem.
%
% The MDP problem is introduced in the following paper:
%
% James M. Crawford, Michael J. Kearns, and Robert E. Schapire. The minimal
% disagreement parity problem as a hard satisfiability problem. Technical
% report, Computational Intelligence Research Lab and AT&T Bell Labs, February
% 1994
%
% and also described at the following URL:
%
% http://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/PARITY/descr.html
%
% We are given a set of input/output samples of a Boolean function of arity n,
% where said function outputs the parity of a fixed but unknown subset of its
% input variables.  A stated number, k, of the sample outputs are incorrect
% with respect to this function.
%
% The goal of the MDP problem is to find a subset of the n variables, where an
% n-ary Boolean function returning the parity of that subset agrees with at
% least n − k of the samples.
%
% The original MDP problem is a satisfaction problem, where each instance has a
% known, fixed error rate (generally 1/8, or sometimes 1/4).  In this variant,
% instances have an unknown (but bounded) error rate, and we want a solution
% that minimizes the number of errors.
%
%==============================================================================

int: num_vars;
set of int: VARS = 1..num_vars;

int: num_samples;
set of int: SAMPLES = 1..num_samples;

int: max_errors;

array [SAMPLES, VARS] of bool: sample_inputs;
array [SAMPLES] of bool: sample_outputs;

constraint assert(max_errors >= 0, "max_errors can't be negative");
constraint assert(max_errors <= num_samples,
    "max_errors can't be greater than num_samples");
constraint assert(num_vars > 0, "num_vars must be positive");
constraint assert(num_samples > 0, "num_samples must be positive");

array [VARS] of var bool: parity_bits;

% In the absence of noise computed_parities = sample_outputs
array [SAMPLES] of var bool: computed_parities;

constraint forall(s in SAMPLES)(
    computed_parities[s] = xorall(v in VARS)(
        parity_bits[v] /\ sample_inputs[s,v])
);

var 0..max_errors: num_errors = sum(s in SAMPLES)(
    bool2int(sample_outputs[s] != computed_parities[s]));

solve :: bool_search(parity_bits, input_order, indomain_max, complete)
    minimize num_errors;

output [
    "The parity bits ", show([bool2int(parity_bits[v]) | v in VARS]), "\n",
    "disagree with ", show(num_errors),
    " out of ", show(num_samples), " samples ",
    "(max allowed is ", show(max_errors), ").\n",
    if fix(num_errors) > 0 then "Disagreeing samples:\n" else "" endif
    ] ++ [
    if fix(sample_outputs[s] != computed_parities[s])
    then
        show(s) ++ ": parity("
        ++ show([bool2int(sample_inputs[s,v]) | v in VARS]) ++ ") = "
        ++ show(sample_outputs[s]) ++ "\n"
    else ""
    endif | s in SAMPLES ];
