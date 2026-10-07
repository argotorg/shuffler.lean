<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# SAW dependency review

The scripts, harness, and reports here use GPL-3.0-or-later. This experiment
does not use CompCert compiler code, Alt-Ergo, or a solver under
non-commercial terms.

The selected SAW release is 1.5, source commit
[`957290e76d916986902ef5bb6ae664090c8295eb`](https://github.com/GaloisInc/saw-script/tree/957290e76d916986902ef5bb6ae664090c8295eb).
The upstream `saw-1.5-ubuntu-22.04-X64.tar.gz` archive has SHA-256
`ca8a2bc81caee606f03ec538b0f5cf299ea4571b65a9812553b15fb37d014826`.
It contains no bundled solver executables. The Nix expression uses this
archive in place of Nixpkgs' default `with-solvers` archive.

| Selected component | Terms |
| --- | --- |
| SAW 1.5 | BSD-3-Clause |
| Clang/LLVM 20.1.8 | Apache-2.0 with LLVM exception |
| Z3 4.16.0 | MIT |
| Yices 2.7.0 | GPL-3.0-or-later |
| GCC 15.3.0 allocation source | GPL-3.0-or-later with GCC Runtime Library Exception 3.1 |
| range-v3 0.12.0 | Boost Software License 1.0 |
| solc source | GPL-3.0-or-later, as documented by the parent test suite |
| GHC 9.6.7 and its runtime libraries | BSD-style GHC terms; the GMP dependency has its own terms |
| GMP | LGPL-3.0-or-later or GPL-2.0-or-later |
| glibc | LGPL-2.1-or-later for the linked runtime libraries |
| ncurses/tinfo | MIT-style terms |
| zlib | zlib license |

The selected Nixpkgs source remains the repository's existing locked input,
commit `c7def046b9a883d46974757852106483d741586f`, with `allowUnfree = false`.
The shell selects the two solver packages explicitly. No optional solver
is discovered from a downloaded bundle.

The upstream release workflow uses `cabal.GHC-9.6.7.config` as its freeze
file. All 350 package/version entries were checked. Of these, 345 have
Hackage Cabal metadata: 257 use BSD3/BSD-3-Clause, 50 MIT, 21 BSD2/BSD-2-Clause,
12 ISC, three PublicDomain, one LGPL, and one GPL-2.0-or-later. The five
remaining entries are GHC's `ghc-boot`, `ghc-boot-th`, `ghc-heap`, `ghci`, and
`rts`; they use the GHC distribution license. The complete reviewed list
and primary URLs are in [hackage-licenses.json](hackage-licenses.json).

The pinned Git submodules and their license sources are listed in
[submodule-licenses.json](submodule-licenses.json). The Haskell submodules
use BSD-style terms. The separate mir-json Rust source declares MIT or
Apache-2.0; this experiment does not run mir-json. Native LMDB code in the
Haskell binding also has OpenLDAP Public License terms and an ISC-derived
notice. The bundled libBF C code has MIT terms. These additional native
licenses permit commercial use.

`readelf` on the installed SAW executable reported only `libm`, `libtinfo`,
`libz`, `libgmp`, and `libc` as dynamic library dependencies. Their terms
are listed above. No solver is dynamically linked through those entries.

This review checks the release's dependency declarations, pinned source
license notices, and dynamic library list. It is not a reproducible-build
proof that the upstream binary contains exactly those source versions.
The exact archive hash is fixed, and no new verifier binary is copied into
the repository. If tool binaries are distributed later, retain all required
notices and meet their source-distribution obligations.

The four GCC runtime source files are fetched from commit
[`4db0e8df15bef836558857c291c323add11d035c`](https://github.com/gcc-mirror/gcc/tree/4db0e8df15bef836558857c291c323add11d035c).
Their original GPL and Runtime Library Exception notices stay unchanged.
The hashes and exact filenames are in [fetch_runtime.py](fetch_runtime.py).
This source is used only to give the verifier the actual allocation and
deallocation bodies.
