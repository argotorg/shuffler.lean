<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Frama-C target initialization

The unchanged production C now has nine valid focused obligations for
the fill invariant and target initialization. The parentheses control
also has nine valid goals. Removing the target store leaves the named
fill-invariant preservation goal unproved. All three expected outcomes
pass in [results.json](results.json).

The added WP strategy instantiates the existing surjection premise at the
index in the goal's outer array access. It adds no assumption. The first
strategy searched inside the memory expression and selected zero from an
earlier store. The final strategy selects the requested index. The
annotation step checks that all C tokens are preserved.

The actual runner command is used by the controls. It sets the local
Why3 configuration and prover selection in the stage that runs WP, after
`-then`. Earlier focused commands that set the prover selection only
before that boundary did not run the requested tactics. The proof stage
uses WP tactics, CVC5, and Z3. No Alt-Ergo is used.

The [baseline report](baseline/goals.json),
[baseline script](baseline/session/script/permute_loop_invariant_target_initialized_established.json),
and [changed-store report](missing-target-store/goals.json) are retained.
The changed-store result is proof rejection, not an SMT counterexample.
The [unit-test log](unit-tests.log) records 25 passing tool tests.

These focused results do not establish the full memory or functional
contract. In particular, the main-loop termination obligation is still
open. The full memory pass must also check every invariant and runtime
obligation, not only these selected properties.

Each case retains the source, annotated copy, command, goals, proof
scripts, solver obligations, and diagnostics. The `diagnostics` directory
also retains the isolated helper failure, its successful instantiation,
and the seven-goal production diagnostic that preceded the controls.
[archive.json](archive.json) records 86 checked file hashes.
The build is `spikes/clight-permute/build/frama-c/initialization-controls/`.
