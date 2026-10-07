<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# SAW equivalence checks

This checker runs the actual generated C and the actual pinned solc C++
oracle on equal inputs. It proves that their status, final or partial data,
trace length, written trace prefix, blocked position, and excess depth are
equal. Each run fixes a valid permutation and leaves every input value
symbolic over all 32-bit unsigned values. Duplicates are included.

This is a finite-case LLVM proof attempt. It is not a proof for every
permutation through length 1024. The mathematical Rocq proof has a separate
scope. Runtime and source-translation assumptions are listed below.

## Run

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/tests/equiv-saw/shell.nix'
python3 spikes/clight-permute/tests/equiv-saw/verify.py --max-n 3 --timeout 2400
python3 spikes/clight-permute/tests/equiv-saw/mutations.py
python3 spikes/clight-permute/tests/equiv-saw/completion.py
python3 spikes/clight-permute/tests/equiv-saw/test_driver.py
```

`--max-n` enumerates every valid permutation from length one to the given
length. Its supported range is one through five. To select one permutation:

```sh
python3 spikes/clight-permute/tests/equiv-saw/verify.py --permutation 2,0,1
```

Use `--core FILE`, `--oracle FILE`, or `--oracle-includes DIRECTORY` to
check an explicit source variant. The last option selects the copied solc
definitions for a mutation test; the default uses the hash-checked pinned
definitions. Production files are never edited. `--out DIRECTORY` keeps
each experiment separate. `--build-only` generates the LLVM and proof
scripts without making a proof claim.

`--negative-control` changes one output value in a separate miter build.
It must fail. The mutation matrix changes each source in a separate copy.
For faulty variants it requires a solver counterexample; a timeout or
build error does not count as detection. Equivalent variants must pass.

Logs, generated SAW scripts, source hashes, compiler commands, LLVM files,
and JSON results are kept below `build/equiv-saw`. A proof result requires
successful SAW exit, its final proof-success message, and no partial-result
message. A timeout or partial execution is incomplete, even if some
branches were checked. The runner clears old results before each build.

## Current evidence

The first trial proved both length-two permutations, plus length-three
permutations `[0,1,2]` and `[0,2,1]`, with arbitrary full-width values.
The other four length-three cases exceeded a 180-second trial limit.
They did not produce a counterexample. A longer run is recorded separately
under `build/equiv-saw/full-n3`; consult its results before extending the
scope claim.

The mutation trial rejected all 12 faulty source variants with explicit
solver counterexamples and proved both equivalent changes. The separate
data-increment negative control failed with input `[0,4294967295]`.
These are checks of the proof harness. They are not a claim that mutation
testing covers every possible defect.

The completion controls found that SAW 1.5 can report proof success after
`exit(0)` on one symbolic branch. It prints `Symbolic simulation completed
with side conditions.` and checks the remaining return paths. The runner
now rejects that message. The unchanged length-two case passes; variants
with `exit(0)` in the C body or actual solc body are both classified as
incomplete. A failed-build control also checks that a prior success record
cannot remain in the results file. This guard depends on the pinned SAW
version and its normal information output; review it when changing SAW.

An optional `--partition-values` mode represents equal values by one
shared symbolic word and requires the distinct representative words to be
in increasing order. It enumerates every order with ties. A separate
Z3 proof shows that every input can be reconstructed from one of these
representative classes. The equivalence checks must all pass as well;
the coverage theorem alone proves no program equivalence. This mode is
an experiment to reduce path cost, not a restriction to small data values.

## Exact proof and runtime boundary

The C core is compiled as C11 at `-O1`. The oracle is compiled as C++20 at
`-O0`, with `-Xclang -disable-O0-optnone`. Both disable loop and SLP
vectorization. LLVM's `lower-constant-intrinsics` pass lowers
`llvm.is.constant`, which the selected SAW release does not implement.
The source algorithm, vector implementation, range-v3 sorting, and active
oracle assertions are retained. No replacement sorting algorithm is used.

An earlier `-O1` oracle run failed SAW's memory-load check on an aggregate.
The checker therefore uses the source compiler's `-O0` form. It does not
enable lax memory options or ignore that failure. Neither form alone gives
a general ISO C or C++ undefined-behavior theorem. SAW/Crucible's documented
poison and `freeze` limits remain relevant, as does trust in Clang and the
LLVM lowering pass.

The bitcode includes the unchanged GCC 15.3.0 implementations of ordinary
new, nothrow new, ordinary delete, and sized delete. `fetch_runtime.py`
checks their exact source hashes. Thus these functions are executed rather
than replaced by a user-assumed SAW contract.

The execution still uses Crucible's built-in `malloc`, `free`, memory-copy,
and assertion models. In particular, its `malloc` model allocates fresh
storage; it does not model allocation failure. The comparison therefore
assumes successful allocation, the default allocator functions, no custom
new-handler effects, and no allocation exception. C++ allocation failure
has no matching behavior in the allocation-free C core. Do not silently
extend this result to that case.

`allocation_failure.sh` checks this boundary against the unchanged core
and oracle. It runs the C call, then makes the next C++ allocation throw
`std::bad_alloc`. The observed result is C success and a C++ exception.
This is a test of the stated runtime assumption, not a failure of the
algorithm equivalence within that assumption.

All six C buffers are separate local arrays. Only the input arrays are
initialized before the C call. The miter compares only the written trace
prefix and bounds its length first. The input permutation is a literal
valid permutation. No input precondition excludes particular values in
the default mode. There are no user overrides or assumed algorithm
contracts, and there is no loop bound in the generated SAW proof.

Path satisfiability checking is enabled. The selected SAW default uses Z3
for that step; the proof script also selects Z3 for the final obligations.
SAW 1.5 checks for Yices when path checking starts, even with its Z3 default,
so the shell supplies both solvers. It may discard
infeasible paths established by the solver; it must not discard feasible
paths to produce a successful result. Unknown calls on a feasible path,
memory failures, and assertion failures cause proof failure. A tool timeout
produces no proof for that case. Early process exit is a separate case:
SAW can report proof success for surviving paths, so the runner must also
reject its partial-result message as described above.

## What is needed for length 1024

Enumerating permutations or orders with ties cannot scale to this size.
A full proof needs contracts and invariants for the actual C++ library
operations, then a relation between their states and the C arrays. In
particular, it needs stable sorting and group/set-difference specifications,
vector allocation and size invariants, the duplicate pairing relation, and
the swap-loop relation including partial traces and blocked outputs.

SAW's experimental cutpoints can support loop invariants, but they establish
partial correctness. A termination argument is also needed. Inserting
proof cutpoints would need a checked connection to the unchanged program.
No such invariant development is included in the present checker. The
current all-size Rocq model theorem does not verify those C++ library
bodies and cannot simply be used as an assumed override for them.

See [LICENSES.md](LICENSES.md) for the selected dependency terms.
