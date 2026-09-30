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

The implementation is in `Shuffler/BuildBottomUp/Defs.lean`.
`Shuffler/BuildBottomUp/Termination.lean` contains the invariant, execution model,
step contract, and termination measure. The proofs are in
`Shuffler/BuildBottomUp/Lemmas`, with the termination theorems and verified
wrapper in `Lemmas/Verified.lean`.
The tests call these modules directly and include 6,527 cases with enumerated
stacks, mappings, and cursors.
