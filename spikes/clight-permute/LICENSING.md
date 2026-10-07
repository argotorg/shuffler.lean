# License boundary

This directory selects **LGPL-2.1-or-later** for every copied CompCert
source. It does not select CompCert's non-commercial license. The new
implementation, proof, printer, and build files use **GPL-3.0-or-later**,
unless a file gives a different license. The GPL text is in `LICENSE`.
Original notices on copied sources remain in place.

The five proof modules in `../rocq-permute` are also new GPL-3.0-or-later
code from this development. Their SPDX notices select that license; the
license text is in that directory's `LICENSE` file as well. The Clight
proof build imports those modules under the `Legacy` namespace.

## Pinned CompCert files

The source is the official CompCert 3.17 release at commit
[`7b1f02b09954b9b916eb2a91d283c9b5355bf172`](https://github.com/AbsInt/CompCert/tree/7b1f02b09954b9b916eb2a91d283c9b5355bf172).
`vendor/compcert.sha256` lists the digest of each copied file.
`audit-deps.py` has a separate, exact file allowlist.

The original [`LICENSE`](vendor/compcert/LICENSE) explicitly offers the
LGPL alternative for these groups:

| Copied group | License provision |
| --- | --- |
| Eight files in `lib/` | All files in `lib/` |
| Twelve files in `common/` | All files in `common/` |
| `Clight.v`, `ClightBigstep.v`, `Cop.v`, `Ctypes.v` | Each file is named |
| `Clightdefs.v`, `Ctypesdefs.v` | All files in `export/` |
| `x86/Builtins1.v`, `x86_64/Archi.v` | These architecture file names are named |

These 28 modules contain the transitive CompCert imports of `Clight`,
`ClightBigstep`, `Clightdefs`, and `Ctypesdefs`. Their remaining source
imports come from Rocq's standard library and Flocq. The source files
are unmodified. They compile with Rocq 9.1.1 and Flocq 4.2.2.

The build copies this source set into `build/compcert` and runs `coqdep`
and `coqc` on that set. It does not fetch the full CompCert repository.
It does not run CompCert's Makefile, configure script, extraction script,
compiler passes, compiler driver, `clightgen`, or `ccomp`. In particular,
the LGPL status of upstream `extraction/extraction.v` would not authorize
its non-commercial imports; that file is not used here.

`audit-deps.py` checks the exact files, their digests, their Rocq imports,
and their transitive closure before each dependency build. It also checks
the project imports against explicit project, CompCert, and legacy module
lists. The generated CompCert directory may contain only allowed sources
and their normal Rocq build files. An unexpected file or symlink causes an
error. A changed or missing source invalidates its compiled dependency
cache before the source set is copied again; timestamps alone cannot hide
a changed source. Its negative tests check added files, changed bytes,
unapproved imports, dynamic loads, string/comment boundaries, stale build
inputs, and a changed manifest. This check protects against accidental expansion.
A deliberate change to both the script and the manifest still needs human
license review.

## Other dependencies

`shell.nix` reads the repository's `flake.lock` directly. It pins Nixpkgs
to `c7def046b9a883d46974757852106483d741586f` and refuses packages marked
unfree. This avoids the worktree Git hash error from `getFlake` on `.`.
The main direct dependencies have these licenses:

| Dependency | Version in the pinned shell | Terms |
| --- | --- | --- |
| Rocq | 9.1.1 | LGPL-2.1 |
| Rocq Stdlib | 9.0.0 | LGPL-2.1 |
| Flocq | 4.2.2 | LGPL-3.0-or-later |
| MathComp | 2.5.0 | CeCILL-B |
| OCaml | 4.14.4 | LGPL-2.1 with the OCaml linking exception |
| OCaml Findlib | 1.9.8 | MIT |
| GCC | 15.3.0 | GPL-3.0-or-later; runtime libraries have their own exceptions |
| Clang/LLVM | 21.1.8 | Apache-2.0 with the LLVM exception |
| Python | 3.14.7 | Python Software Foundation license |
| curl | 8.22.0 | curl license |
| range-v3 | 0.12.0 | Boost Software License 1.0 |

The coverage-guided tests use LLVM's libFuzzer runtime, `llvm-cov`, and
`llvm-profdata` from the pinned LLVM 21.1.8 packages. These use Apache-2.0
with the LLVM exception. They add no non-commercial restriction and import
no CompCert compiler code. The new harness and coverage scripts are
GPL-3.0-or-later.

The second fuzzing engine is AFL++ 5.00c from the same Nixpkgs pin. Its
package contains Apache-2.0 and AGPL-3.0-or-later code. We select the free
license grants, which permit commercial use; the optional commercial
license is not used. The upstream `LICENSE` and `README.md` state these
terms. `instrumentation/afl-compiler-rt.o.c` has an Apache-2.0 SPDX notice.
The AFL++ test executable also links `libAFLDriver.a`; retain the package's
license and corresponding-source obligations if distributing that test
executable. It is separate from the generated production C and the Rocq
proof dependencies. Nixpkgs selects upstream tag `v5.00c`, with source hash
`sha256-lox5UYCSjp4Vu6oBc5+wZDBAufGaCiVxJqp74LDrw8k=`. This selection is
recorded in `pkgs/tools/security/aflplusplus/default.nix` at the Nixpkgs pin.

Flocq remains a proof dependency even though this program uses only
integers. Clight's semantics includes floating point definitions.

The Fil-C tests use the official 0.686 musl package. Its compiler and C++
libraries use Apache-2.0 with LLVM exceptions, its runtime uses BSD terms,
and its musl libraries use MIT and the retained permissive notices. The
package and license-file hashes are recorded in
[tests/FILC_RESULTS.md](tests/FILC_RESULTS.md). This test toolchain is
separate from the production printer and Rocq dependencies.

The solc test oracle uses upstream Solidity source under GPL-3.0-or-later;
its pinned source and extraction boundary are documented with the tests.
None of these licenses limits use to non-commercial activity.

The new code can be distributed under GPL-3.0-or-later. Keep the LGPL
source licenses and notices, provide the corresponding source, and meet
the relevant GPL/LGPL distribution terms. A GPL label on new code does
not change the license of an imported file. Review changes to the source
allowlist, extraction imports, or test oracle before accepting them.

## Trust is separate from licensing

The CompCert memory model imports functional extensionality and its
`proof_irr` axiom. `Archi.v` also has the target parameter `win64`.
Proof reports must show the actual assumptions of their theorems.
For example, `Print Assumptions execute_sound` reports classical logic,
functional extensionality, two classical real-number decision assumptions,
and CompCert's `external_functions_sem` and `inline_assembly_sem` parameters.
The restricted interpreter has no external-call or assembly case. These
parameters enter through the type of the full upstream execution relation.
Do not describe this development as axiom-free.
The selected build is for the x86-64 architecture definitions; the C
contract selects Linux and the normal system ABI. A license check is
not a proof that this target or a printed program is correct.

## Commands

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
python3 spikes/clight-permute/test-audit.py
sh spikes/clight-permute/build-deps.sh
```

From `spikes/clight-permute`, compile project modules with
`coqc -R build/compcert compcert Module.v`. `fetch-deps.py` can restore
only the exact pinned files. Normal builds use the vendored source and
do not run that fetch step.
