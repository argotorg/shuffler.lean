# Zig shuffler verification

This package contains a partial proof of the compiled Zig shuffler and the tools
used to generate and check its proof obligations. It is independent of the Lake
package in the parent directory.

There are 31 compiled functions. The paused campaign has closed final contracts
for 21 functions. The proof of `shuffle` and the full composition are open.
See [STATUS.md](STATUS.md) for the exact scope and
[Review/Closed.lean](Review/Closed.lean) for the checked final statements.

The target specification is `Lift.Shuffler.Spec.run`, over the Zig model in
`Lift.Shuffler.Zig`. This work does not prove that this model has the properties
of the upstream C++ model. The copy in `Lift/Shuffler/Ext` retains the upstream
`FlatShuffler` namespace; it is not a proved bridge between the models.

## Check the proofs

Use Linux x86-64, Python 3.11 or later, Git, and Elan. Run commands from this directory.
Elan selects the exact toolchain in `lean-toolchain`:

```text
leanprover/lean4-pr-releases:pr-release-16310-81f2735
```

Use Elan's `lake` command. Check that `lake --version` reports Lean 4.37.0-pre
before the build; an existing development shell can select another compiler.

```sh
export LEAN_NUM_THREADS=2
python3 -B scripts/build.py
python3 -B -m unittest discover -s scripts -p 'test_contract_gate.py'
python3 -B scripts/check_source.py
```

The build script checks source modules in dependency order, with one Lake build
at a time. It removes inherited Lean search paths and disables the Lake artifact
cache. Each module has a 600-second limit. Build logs and a receipt go to
`local/build/`, which is ignored by Git. `lake build` also checks the default
`Review` target, but can run more build jobs at once.

`Review.Closed` states each final theorem at its expected contract type and runs
the production axiom gate. A final theorem cannot retain an extra hypothesis.
The gate rejects `sorryAx`, added axioms, and `native_decide`. It permits the
three standard Lean axioms and checks each permitted `bv_decide` certificate.
This does not establish that the contracts express the intended user behavior;
the contracts and models need review too.

No model account, key, campaign journal, or paid call is needed for these checks.
The exact Kraken and Loogle source snapshots are in `vendor/`. Their file hashes
are part of the recorded source.

## Check the Zig source

The copied source is byte-equal to
`libyul/backends/evm/ssa/stack/shuffler.zig` at Solidity commit
`b86f67bd4cc712eda85b937f0090b4b820ed6360`. Its SHA-256 is:

```text
fd2d09d73e1224ff06449ac9560907a32382b18be2f47f18c9423e332dcd07e6
```

The assembly is embedded as a literal in `Lift/Shuffler/Code.lean`.
`check_source.py` checks the source and assembly hashes and compares that literal
with the assembly file. To reproduce the assembly, install the exact Zig 0.17.1
compiler, then run:

```sh
python3 -B scripts/check_source.py --rebuild --zig /path/to/zig
```

The separate `source/solidity-zig` submodule records the source revision. The
source branch must be public before colleagues can initialize it. The proof
build uses the included source and does not require submodule initialization.
After the branch is public, run from the parent repository:

```sh
git submodule update --init zig-verification/source/solidity-zig
cd zig-verification
python3 -B scripts/check_source.py --require-source
```

The existing parent `solidity` submodule remains the C++ fuzz oracle at its
previous revision. The two source pins have separate purposes.

## Build and check the tools

The optional tools need a C compiler, libcurl headers and library, `timeout`,
and `setsid`. The terminal view uses only the Python standard library.

```sh
python3 -B scripts/build.py --facet o Skel.Main Skel.Test.Main SkelNeeded NxLift.LeanWorkerMain Review.Contracts Main Test LoogleMain
lake build skel skel-test lean-worker @leantools/leantools @leantools/tests @loogle/loogle
export PATH="$PWD/scripts:$PATH"
lake env .lake/build/bin/skel-test --only provepar,full,recover,answerexport,regiontasks --jobs 1
python3 -B -m unittest discover -s Skel/Test -p 'test_watch*.py'
```

See [VALIDATION.md](VALIDATION.md) for the checks made on this export and their
limits. The worker guide is [KRAKEN.md](KRAKEN.md). It includes the heap, byte,
frame, loop, and call tactics available to proof workers.
The `scripts/leantools` wrapper selects the package's worker binary and vendored
Loogle binary. Put it first on PATH when you use the campaign tools, so they use
this package's worker.

For a generation-only audit of all 31 functions, after building the tools:

```sh
python3 -B scripts/generate.py
```

The audit calls the production statement-shape reader and generators. It writes
the generated obligations into four batch directories and the combined receipt
and graph to `local/generation/`. Each batch has a 120-second limit. It does not call a
model or change the included final proof files. `skel full --dry` is different:
it runs the local proof pipeline and can write `Lift/Shuffler/Proved` modules.
Use a separate checkout for campaign trials.

## Run a campaign

Paid execution is opt-in. This export contains no active budget, credentials,
or old worker traces. The files in `examples/` are templates; set the endpoint,
model, token prices, limits, and the named key variable before use. Use
`leantools tools` and the CLI help to inspect current parameters. Add model
flags only when you intend to permit paid calls.

The scheduler shares model slots across functions and across ask/prove jobs.
`--ask-parallel` sets that shared bound. `--procs` limits local Lean checks to
1–3. More model slots also need memory for proof workers. The campaign code
includes recovery checks; `--resume RUN` validates saved closed rows against
the current generated input before reuse. A resume requires that run's journal
and saved files, which are not included in this source export.

To watch a campaign from this directory:

```sh
python3 -B Skel/watch.py .skel/runs/RUN --view workers
```

Use `--view deps`, `--view cfg --fn shuffle`, or `--view rows` for other views.
Use `--once` for plain text. Both ask jobs and proof workers appear in the
worker view. `lake exe skel graph --out local/graph.json` writes the call graph.

Source origin, export changes, and license status are recorded in
[PORTING.md](PORTING.md) and [LICENSES.md](LICENSES.md).
