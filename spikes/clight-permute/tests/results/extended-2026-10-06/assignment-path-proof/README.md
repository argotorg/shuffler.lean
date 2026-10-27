<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Assignment proof for control paths

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

The later [execution proof](../assignment-execution-proof/README.md)
connects this result to terminating Clight execution. This archive keeps
the earlier control-path evidence unchanged.

The candidate checker now has a statement-level proof against an explicit
control-path model. `AssignmentSound.v` defines that
model on actual Clight statements. Both condition branches are possible.
Each path records temporary assignment names and a Boolean that includes
the read checks at every reached expression. That Boolean can be false.

`complete_path_safe` proves safety and the assignment guarantees at each
exit. `prefix_safe` also covers finite prefixes without a termination
premise. This includes later loop iterations. `checked_function_prefix`
starts with the function parameter names. `permute_prefix_safe` applies
the result to the actual Permute body.

Five witnesses include an unsafe self-copy, an unassigned else path, a
zero-iteration loop exit, a statement after an inner break, and a later
iteration. They check that these paths are present in the model. The
later-iteration witness uses unconstrained branch choices; it does not
state that one fixed C input makes those choices.

`SoundContract.v` checks four public theorem types.
The theorem assumptions (`AssignmentSound.log`) and
contract assumptions (`SoundContract.log`) are closed under the global
context. The kernel check (`kernel.log`) passes. The
kernel policy (`kernel-policy.log`) finds 12 allowed upstream axioms and no
unsafe typing settings in the imported context.

This archive proves the stated control-path result. It does not yet link
that model to concrete Clight execution. Memory validity, initialized
bytes, declaration rules, and the C translation remain separate. The
checker is not in the production pipeline. F7 remains open.

`results.json` records build and source hashes.
`archive.json` records the retained files. All source and
artifact hashes were checked before this archive was made. The build is
`spikes/clight-permute/build/initialization/prefix-model-checked-v3/`.
