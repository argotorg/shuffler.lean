# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Then run `lake build` to compile the project.

Run `lake build Tests` to check the proofs and regression tests.

## Build bottom up

`Shuffler.BuildBottomUp.buildBottomUp` runs the checked algorithm.
`Shuffler.BuildBottomUp.buildBottomUpVerified` takes an `Invariant` and returns
`Except ShuffleErr`. Its proofs establish termination and exclude assertion
errors. They do not prove that the result equals the target: the input invariant
does not require mapped source values to equal target values.

The implementation and its proof dependencies are in `Shuffler/BuildBottomUp`.
The tests call these modules directly and include 6,527 cases with enumerated
stacks, mappings, and cursors.
