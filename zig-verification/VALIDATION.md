# Export checks — 2026-11-25

These checks use this independent package and its pinned Lean toolchain. They
do not restart the paid campaign. The campaign remains paused.

## Proof boundary

The 21 closed final proofs and their dependencies compile from source. This
checks 190 source modules. No source-workspace `.lake` artifacts were copied.
The build removes inherited Lean search paths and disables Lake's artifact
cache. `validation/proof-build.json` records the module results.

`Review.Closed` assigns each final theorem to its expected contract type. All
21 wrappers pass the production axiom gate. The gate checks the permitted
`bv_decide` certificates again. `validation/axioms.json` records the actual axiom
names. The 21 accepted proof files retain their original source hashes.

The first wrapper audit found an export naming error: the final theorem names
needed `.skel_semantic.final`. The wrappers were corrected; proof source and
contract types were not edited. The corrected audit passes.

All 31 contract modules compile through `Review.Contracts`. Its first build
found that the Lake library list contained only `Review.Closed`. Adding the
contract module to that list resolves the build error.

The contract-gate tests have five passing cases. They check acceptance of a
closed proof and rejection of a hole, an added axiom, a forged bit-vector
certificate axiom, and an extra assumption.

## Source boundary

The source check confirms the Zig source hash, the assembly hash, and equality
between the assembly file and the Lean assembly literal. A rebuild with Zig
0.17.1 produces the same assembly bytes. The source bytes also match the blob
at Solidity commit `b86f67bd4cc712eda85b937f0090b4b820ed6360`.

Ten Python boundary tests pass. These cover dependency order, executable
prerequisites, missing source, import cycles, check time limits, changed source,
changed embedded assembly, and an absent required source submodule.
Six native-port tests pass. The four native fixture bodies retain their source
hashes; only their source-identity headers change.

The worker-wrapper test first fails with an inherited foreign project root.
It passes after the wrapper sets this package's root and clears inherited Lean
search paths. The check runs the actual shell wrapper with a test Lake command.

The exact Solidity revision still needs publication by the owner. The proof
build and CI use the included source and do not need that submodule initialized.
After publication, use `scripts/check_source.py --require-source` to check the
initialized source pin. This export has no new C++ source pin or proof of a
bridge to the parent repository's model.

## Terminal views

The Skel terminal tests pass 65 cases. The coordinator terminal tests pass 49
cases. They cover stored test fixtures; they do not replay a paid campaign.

## Obligation generation

`python3 -B scripts/generate.py` passes for all 31 functions. Each function has
a typed statement shape, lower obligations, an upper chain, and a final
obligation. The combined receipt is `validation/generation.json`. No model
calls are made and no accepted proof file is written.

The first single-process audit exceeded its 120-second limit after writing
21 function files. The audit now uses four bounded batches. Five Python tests
check the combined receipt's coverage and reject repeated or inconsistent data.
Lean guards test the batch arguments, including invalid and boundary cases.

This audit checks statement shapes and generated text. It does not elaborate
every generated proof file or fill missing invariant and semantic proof text.
The receipt lists the rows that still need such text. Closed-proof checking
and generation coverage are separate results.

## Tool compilation

All 690 source and native modules in the selected tool and test roots build.
`validation/tool-build.json` records the module results. The roots are
`Skel.Main`, `Skel.Test.Main`, `SkelNeeded`, `NxLift.LeanWorkerMain`,
`Review.Contracts`, `Main`, `Test`, and `LoogleMain`.

The source export initially omitted `native-status2.jsonl` and `garbage.lrat`.
Both original fixtures are now included. `Test.Axioms` passes with its original
negative-certificate test. No proof or contract was changed for these fixes.

The local build uses two Lean threads and one module build at a time. It pauses
new builds below 20 GiB available and continues at 24 GiB. No memory pause was
needed in the completed native build. CI uses its runner resources; it does not
apply this machine's memory floor.

All six named executable link checks pass: `skel`, `skel-test`, `lean-worker`,
`@leantools/leantools`, `@leantools/tests`, and `@loogle/loogle`.
The five core Skel suites pass: `provepar`, `full`, `recover`, `answerexport`,
and `regiontasks`.

The package's worker wrapper passes schema listing, source viewing, a scratch
`#check True`, and a Loogle query for `Mem.loadInt`. It starts a daemon for this
package and stops that daemon after the checks. The daemon file is removed.
The source workspace's daemon is not stopped. `validation/worker-smoke.json`
records these results.

All five worker test commands pass: `--prove`, `--validation`,
`--module-validation`, `--holes`, and `--concurrency`. Each flag was run as a
separate command. No paid model calls were made.

An additional batch selected 14 Skel suites for call summaries, generation,
mixed-width values, source and rendering, statement shapes, and worker checks.
It did not finish within its 1,200-second outer limit. It produced no complete
suite summary, so these 14 suites are not recorded as passed. Its remaining
owned worker was stopped after the timeout. The limits were not raised and the
batch was not repeated. `validation/tool-checks.json` records the exact selected
suites and the timeout, as well as the passed link, core, and worker commands.
CI selects the five core Skel suites; it does not run this additional batch.

## Commands

Run from this directory with `LEAN_NUM_THREADS=2`:

```sh
python3 -B scripts/build.py
python3 -B scripts/check_source.py
python3 -B scripts/generate.py
python3 -B -m unittest discover -s scripts -p 'test_*.py'
python3 -B -m unittest discover -s Skel/Test -p 'test_watch*.py'
python3 -B -m unittest discover -s Coordinator/Test -p 'test_*watch.py'
```

Build logs and test state remain in ignored local directories. Compact receipts
are in `validation/`. `SOURCE-MANIFEST.json` records the original copied hashes;
`PACKAGE-MANIFEST.json` records the final package hashes.

## Limits

The 21 checked contracts do not establish a full proof of `shuffle` or full
composition. Ten function finals remain open. The contracts and models also
need review. See `STATUS.md`.

Linter and deprecated-name warnings remain. These checks do not promote those
warnings to errors. No proof heartbeat limit was raised for this export.

The new GitHub workflow is configured but has not run on GitHub. The parent
package's Lake files, toolchain, source files, and existing C++ submodule pin
are unchanged. Its build and tests were not repeated for this export.
