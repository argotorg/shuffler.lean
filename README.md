# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Then run `lake build` to compile the project.

Run `lake build Tests` to check the proofs and regression tests.

## Build bottom up

`Shuffler.BuildBottomUp.buildBottomUp` runs the checked algorithm from target offset zero.
`Shuffler.BuildBottomUp.buildBottomUpVerified` takes an `Invariant 0 state` and returns
`Except ShuffleErr`. Its proofs establish termination and exclude assertion
errors. They do not prove that the result equals the target: the input invariant
does not require mapped source values to equal target values.

The implementation is in `Shuffler/BuildBottomUp/Defs.lean`.
To review the termination claim, read `Shuffler/BuildBottomUp/Termination/Defs.lean`
and `buildBottomUp_terminates` in `Shuffler/BuildBottomUp/Termination/Theorems.lean`.
The statement uses Lean's standard `Acc` certificate:

```lean
Acc (Continues (loopParts source target spills).val) ((none, 0), state)
```

`Continues body next current` means one body call from `current` returns
`.yield` with the control value and state in `next`. The next configuration
comes first because that is the argument order required by `Acc`.
`Acc` requires a certificate for every successor. Done and error results have
no successors, so they are base cases. An infinite chain of yields cannot have
an `Acc` certificate. This is the certificate used by Lean's general
well-founded recursion machinery; it does not select one terminating execution.
`loopParts` carries an equality that connects the body and exit code to
`buildBottomUp`. The claim requires `Invariant 0 state`.
Both `.done` and error results exit the loop; `buildBottomUp_noAssertion`
separately excludes assertion errors.

`ControlFrame` is this project's name for the pair passed between iterations.
Its named accessors are `result` (an optional early return result) and
`targetOffset` (the current target offset). It remains a pair to match Lean's
generated loop body directly. The proof code also uses `Frame`, which includes
the `StateT` state. Neither name is part of Lean's loop API.

The measure, step contracts, state conversions, and `Acc` proofs are in
`Shuffler/BuildBottomUp/Lemmas`. The executable definition has no termination
proof arguments.
The tests call these modules directly and include 4,675 cases with enumerated
stacks and mappings.
