# Fil-C run, 6 October 2026

The generated C implementation and the pinned solc C++ oracle passed:

- 4,435 exhaustive differential cases, plus boundary and rejected-input tests.
- 100,000 random differential cases, seed `2654435769`.
- Replay of 802 unique retained inputs from libFuzzer, AFL++, and the boundary
  seed set. Empty input also passed. Missing and oversized replay files were
  rejected.

There were no Fil-C errors or result differences in these runs. This was
fixed-seed random testing and corpus replay. It was not a coverage-guided
Fil-C run. The binary package does not include a libFuzzer runtime. Native
libFuzzer or AFL++ runtime objects were not linked into the Fil-C program.

## License check

The official [Fil-C 0.686 release](https://github.com/pizlonator/fil-c/releases/tag/v0.686)
points to commit `163fae598eaf249b74065b0156f3a7e7ba8c0e5a`.
The selected package is `filc-0.686-linux-x86_64.tar.xz`, the self-contained
musl package. Its SHA-256 is
`60bfbe8ee63d7e462394aa8d5e44fee675de892bcf800d9cc80d86378cad6b07`.
This agrees with the digest in the official release API.

The package README identifies these license files. Each was read before use.
The runner checks their SHA-256 digests.

| Component | Terms and source |
| --- | --- |
| Clang/LLVM, libc++, libc++abi, compiler-rt | [Apache 2.0 with LLVM exceptions](https://github.com/pizlonator/fil-c/blob/163fae598eaf249b74065b0156f3a7e7ba8c0e5a/LLVM-LICENSE.txt); retained legacy LLVM and third-party notices also apply. |
| Fil-C runtime and libpas | [BSD 2-clause](https://github.com/pizlonator/fil-c/blob/163fae598eaf249b74065b0156f3a7e7ba8c0e5a/libpas/LICENSE.txt), with a retained BSD 3-clause notice for setproctitle code. |
| User musl and low-level musl | [MIT](https://github.com/pizlonator/fil-c/blob/163fae598eaf249b74065b0156f3a7e7ba8c0e5a/projects/usermusl/COPYRIGHT), including the listed permissive third-party notices. [Low-level musl](https://github.com/pizlonator/fil-c/blob/163fae598eaf249b74065b0156f3a7e7ba8c0e5a/projects/yolomusl/COPYRIGHT) has the same license-file digest. |
| Test sources | New code: GPL-3.0-or-later. solc bodies: upstream GPL version 3 or later. range-v3 0.12.0: Boost Software License 1.0. |

These terms permit commercial use. This run added no noncommercial-only
dependency. License notices remain in the downloaded package. The package
and test binaries stay under ignored `build/filc`. Copies of the run log,
runtime checks, probes, and corpus are saved in `results/filc`. The other programs
in the Fil-C source repository and the `/opt/fil` distribution are not used.
The existing pinned Nix shell supplies build tools with `allowUnfree = false`.
The downloaded host compiler uses host glibc (LGPL); target programs use the
bundled musl libraries.

## What ran

The compiler reports Clang 20.1.8, Fil-C 0.686, the commit above, target
`x86_64-unknown-linux-gnu`, and assertions enabled. Both implementations,
all harness C sources, and reached range-v3 template bodies were compiled
with Fil-C. The C standard was C11; the C++ standard was C++20. The flags
were `-O2 -g -fstrict-aliasing`, with warnings and `-pedantic-errors`.
Assertions stayed enabled. The linker was GNU ld 2.46 from the pinned shell.

The solc revision is `cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`.
`prepare_oracle.py` checked all three upstream source-file hashes, and its
negative tests rejected modified cached sources. The actual generated C
and oracle adapter used these hashes:

```text
a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78  permute.c
4534e19c88f2dfebf132fd47f194b5c5a408f349c9a604f78b651a94bacee15e  tests/oracle.cpp
```

The test buffers keep the existing contract: scratch arrays start without
explicit initialization, and trace comparison reads only the written prefix.
No test or implementation was changed to initialize scratch memory for Fil-C.

The loader lists only bundled `libc++.so.1`, `libc++abi.so.1`, `libc.so`,
`libpizlo.so`, and `libyoloc.so`. The ELF interpreter and runtime search path
point into the local Fil-C package. C/C++ standard headers also come from
that package; the only added host header path is pinned range-v3. Both
implementation object files have Fil-C symbols and runtime references.

Fil-C's [runtime design](https://fil-c.org/runtime.html) includes native code
in `libpizlo`, the loader, startup objects, and low-level `libyoloc`. These
are part of its trusted runtime. The user libc, libc++, libc++abi, generated
C, and oracle are compiled with Fil-C. No native replacement for an
application library was used.

On this Nix host, the downloaded compiler's ELF interpreter path did not
exist. The runner changed that compiler file to use the running shell's
glibc loader. It also ran the package's local setup script. Neither step
changed host configuration or the target runtime model.

## Detection controls and limits

Separate C and C++ probes allocated one unsigned word, then wrote at a
runtime-selected index through a volatile pointer. At index 17 both stopped
with SIGTRAP and `filc safety error: cannot write pointer with ptr >= upper`.
This checks C allocation and C++ vector storage in the actual runtime.

At index 1 both probes exited normally. The reported capability bounds
span 16 bytes for this four-byte allocation. Thus this Fil-C run does not
exclude out-of-bounds writes that stay inside allocation rounding. It also
does not establish the absence of uninitialized reads, integer undefined
behavior, or errors on untested inputs. ASan and MSan results are separate.

## Reproduce and inspect

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix'
sh spikes/clight-permute/tests/run-filc.sh \
  spikes/clight-permute/build/guided/corpus \
  spikes/clight-permute/build/afl/findings/default/queue
```

Omit the two directory arguments to use boundary seeds and any retained
Fil-C snapshot. Optional `PERMUTE_FUZZ_CASES` and `PERMUTE_FUZZ_SEED` select
another random run. The default is 100,000 cases with the seed above.
`FILC_RANGE_INCLUDE` can specify the range-v3 header directory outside Nix.

`build/filc/run.log` records commands and results. `checks/*.libraries.txt`,
`checks/*.elf.txt`, `checks/header-search.txt`, and `checks/bounds-probe-*.log`
record runtime checks. `build/filc/corpus` retains the replay inputs.
The 802-input `corpus.sha256` manifest has SHA-256
`91fc056348cb787889e6ac3424bab0452bcd0e333a57334ac38494b04c1640d6`.
Later corpus snapshots can contain more inputs and have a different digest.

The saved archive `results/filc/corpus.tar.gz` contains these 802 inputs
under `corpus/`. The saved manifest uses paths relative to that directory.
`results/filc/sources.sha256` records the implementation and runner hashes
with paths relative to the repository root.
