# The MiniZinc Benchmark Suite

This is a collection of MiniZinc benchmark instances.

They are derived from models used in the MiniZinc Challenge.

## TODO

**Work in progress! Not ready for general use**

**Note:** Some models will not work with their current data until the next release of MiniZinc.

- [ ] Expand to all Challenge models
- [x] Use LLM to generate descriptions of problems for readmes
- [ ] Review the readmes
- [x] Generate projects openable in the IDE/playground
- [x] Check that models run with current MiniZinc
- [ ] Update models to use best current MiniZinc practices
- [x] Generate metadata for models
- [ ] Generate a searchable website as a catalogue of the benchmarks.

## Structure

- `problems/<problem>/<model>.mzp` A project file which can be opened in the MiniZincIDE or playground
- `problems/<problem>/<model>.mzn` The model file for the problem
- `problems/<problem>/data/<data>.json` The data files in JSON format
- `problems/<problem>/metadata.json` Metadata for the problem

## Quality criteria

All models in this repository should satisfy the following quality criteria:

- Compile successfully with the most recent version of MiniZinc
- Consistent comments
  - Short problem description (not replicating the `README.md`)
  - Comments on "interesting" constraints
- Use idiomatic MiniZinc
  - Use enums and option types where possible
  - Use Boolean variables instead of 0/1 variables
  - Only have domains on defined variables when necessary
- Have no infinite domains (`var int`) in the generated FlatZinc
- Do not use `lb`, `ub`, `dom`, unless well justified (such as in user-defined predicates)
- Do not use multiple model files instead of data files unless absolutely necessary
- Comply with MiniZinc challenge search strategy rules
