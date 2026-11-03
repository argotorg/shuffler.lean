# MemorySanitizer results

Date: 2026-10-06. The unchanged generated C and the actual pinned solc
oracle passed the completed MemorySanitizer checks. No uninitialized-read
report or differential mismatch occurred in the target runs. This is test
evidence, not a proof that all executions are free of memory errors.

| Check | Result |
| --- | --- |
| Deliberate uninitialized-read probe | MSan reported `use-of-uninitialized-value`, gave its heap-allocation origin, and exited 86 |
| Initialized version of that probe | Exited zero without a report |
| Saved libFuzzer corpus | All 482 files executed once; exit zero |
| Saved AFL++ queue | All 364 files executed once; exit zero |
| New libFuzzer campaign under MSan | 73,316 executions in 61 seconds; exit zero |

The saved files contain 802 distinct SHA-256 values. All 846 files were
replayed, including duplicates between the two corpora. The new campaign
used those 802 distinct inputs, seed `73419`, `-max_len=8195`, a ten-second
per-input timeout, and a 60-second campaign limit. It added 284 corpus
units, reported 1,201 executions per second, and used at most 60 MB RSS.
The execution count includes corpus initialization and mutations. It is
not a count of distinct input values.

## Sources and runtime

The target uses the existing `guided.c`, `check_case.c`, and `oracle.cpp`.
The oracle preparation checks the three upstream source hashes at solc
commit `cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912`. No implementation,
printer, proof, or oracle algorithm was changed for this run.

Generated `permute.c` SHA-256:

`a120dccaaa1a7783231f7b4482f76f515ef6c099f4e0e73279f1228e634cfb78`

The compiler is Clang 21.1.8, target `x86_64-unknown-linux-gnu`.
The build uses CMake 4.4.2, Ninja 1.13.2, and Python 3.14.7.
The host is Linux 7.2.8 on x86-64, with glibc 2.42-84.

`build-msan.sh` builds libc++, libc++abi, and libunwind from LLVM
`llvmorg-21.1.8` with `LLVM_USE_SANITIZER=MemoryWithOrigins`. All three
libraries are linked as static archives. The generated Ninja commands
contain MSan instrumentation flags. `llvm-nm --undefined-only` also finds
MSan runtime references in each archive.

The packaged libFuzzer was built against libstdc++. It could not link to
the selected libc++ runtime. The script therefore builds the unchanged
LLVM libFuzzer sources against the instrumented libc++ as well, with MSan
enabled and without coverage instrumentation of the driver itself.
The target sources use `-fsanitize=fuzzer-no-link,memory` and
`-fsanitize-memory-track-origins=2`. No libstdc++ library is linked into the
result. The final executable SHA-256 is:

`424e59aa8ba3e7cac6150503c9c6390de5640935587c8d72fdcc097490fc5953`

System C libraries, the loader, and compiler support remain system
components. MSan's normal interceptors handle supported C library calls.
This is not a fully instrumented operating system. No custom suppression,
ignore list, sanitizer-disable attribute, or blanket unpoison operation
was added. The probe is a separate executable and is never linked into
the Permute target.

## Startup failures and their treatment

The initial setup failed before useful target testing. Slow stack
unwinding through the instrumented unwinder caused recursive MSan error
reporting and a stack-overflow report. The completed runs use frame-pointer
unwinding for allocation and fatal-error stacks. This changes diagnostics;
it does not disable memory checks. The compiler and runtime builds retain
frame pointers. The separate probe then produced the required
uninitialized-read report, and its initialized control passed.

High-entropy address randomization also sometimes places a mapping inside
MSan's reserved address space. This host denies the `personality` call
that MSan uses to restart with ASLR disabled. Linking the executable at a
fixed low address with `-no-pie` reduces this problem; shared libraries
remain dynamic and system ASLR remains enabled. A tested glibc mapping
preference did not remove the issue and is not part of the final setup.

The final runner records and retries only the exact pre-main
`msan_linux.cpp:193` / `ADDR_NO_RANDOMIZE` failure with an empty stack.
It permits at most ten such startup attempts. Any target diagnostic or
other failure stops the run. In the completed invocation, the AFL replay
and the fuzz campaign each needed one startup retry. No target input had
executed in either failed attempt. Earlier setup attempts also produced
mapping failures; they are not counted as test executions or successful
checks.

## Commands and retained evidence

From `spikes/clight-permute`:

```sh
nix develop --impure --expr 'import ./tests/msan-shell.nix' \
  --command sh tests/build-msan.sh > build/msan-build.log 2>&1
nix develop --impure --expr 'import ./tests/msan-shell.nix' \
  --command python3 tests/run-msan.py
```

The second command uses these fixed runtime options:

```text
MSAN_OPTIONS=halt_on_error=1:exit_code=86:symbolize=1:fast_unwind_on_malloc=1:fast_unwind_on_fatal=1
```

`MSAN_SYMBOLIZER_PATH` is the pinned shell's `llvm-symbolizer`. The runner
stores every full argument list, exit code, log path, and startup-failure
classification in `build/msan/commands.jsonl`. The replay manifest records
each original path, snapshot path, byte length, and SHA-256 value. The
completed logs are `probe.log`, `probe-initialized.log`,
`replay-libfuzzer.log`, `replay-afl.log`, and `fuzz.log`. Per-attempt logs
retain the two failed startups. The corpus and artifacts remain under
`build/msan/`. No completed campaign was repeated for this report.

## License boundary

`msan-shell.nix` uses the repository's pinned Nixpkgs input and sets
`allowUnfree = false`. LLVM source is separately fixed at
`llvmorg-21.1.8`, with Nix source hash
`sha256-pgd8g9Yfvp7abjCCKSmIn1smAROjqtfZaJkaUkBSKW0=`.

| Dependency | Terms used here |
| --- | --- |
| Clang, compiler-rt/MSan, libFuzzer, libc++, libc++abi, libunwind 21.1.8 | Apache-2.0 with LLVM exceptions; retained legacy MIT/NCSA notices where applicable |
| CMake 4.4.2 | BSD-3-Clause |
| Ninja 1.13.2 | Apache-2.0 |
| Python 3.14.7 | Python Software Foundation license |
| range-v3 0.12.0 | Boost Software License 1.0 |
| glibc 2.42-84 | LGPL-2.1-or-later, with component notices |
| GCC 15.3.0 compiler support library | GPL-3.0-or-later with GCC Runtime Library Exception 3.1 |
| curl 8.22.0 | curl license |
| Local tests and pinned solc source | GPL-3.0-or-later |

The LLVM runtime license texts were checked in `libcxx/LICENSE.TXT`,
`libcxxabi/LICENSE.TXT`, `libunwind/LICENSE.TXT`, and
`compiler-rt/LICENSE.TXT` in the pinned source. No CompCert compiler,
parser, compiler pass, or non-commercial source is a dependency of these
runtime tests. The separate license audit for producing the C file remains
in `../LICENSING.md`.
