<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Frama-C memory pass with initialization strategy

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

The full memory pass has **641 of 642 explicit goals valid**. Only
`typed_ref_permute_terminates_part2` is unproved. The runner returns
nonzero and records `complete: false`. Read `summary.json`
and `goals.json`.

All other scheduled memory-pass goals are valid, including runtime memory
access, initialization, loop invariants, array frames, and output bounds.
The pass still requires main-loop termination. It is not a complete proof
of the memory contract, and it is separate from the full functional
contract with trace replay and the success condition.

The terminal log counts one extra unreachable goal and prints 642/643.
The reported 641/642 figure counts the explicit JSON entries. All 642 IDs
were checked for uniqueness. The only pending ID was checked again when
this archive was made.

`manifest.json` records the exact command and source hashes.
The source, annotated copy, annotation generator, and runner hashes match.
The [source controls](../frama-initialization/README.md) verify that the
unchanged and parentheses cases pass the selected initialization goals,
while a removed target store leaves its fill invariant unproved.

This archive retains reports, logs, source snapshots, prover configuration,
the CVC5 version adapter, all proof scripts, and selected SMT obligations.
The selected obligations include termination, target initialization, and
the five other goals that were pending in the previous full memory run.
`obligation-hashes.json` lists all 331 generated
SMT files and identifies the retained subset. The other files remain in
`spikes/clight-permute/build/frama-c/memory-target-strategy/`.
`archive.json` records 36 retained file hashes.
