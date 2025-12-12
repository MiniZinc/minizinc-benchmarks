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

- `/<problem>/<model>.mzp` A project file which can be opened in the MiniZincIDE or playground
- `/<problem>/<model>.mzn` The model file for the problem
- `/<problem>/data/<data>.json` The data files in JSON format
- `/<problem>/metadata.json` Metadata for the problem
