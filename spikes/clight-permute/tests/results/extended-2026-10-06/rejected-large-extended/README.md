<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Larger rejection checks at pause

**Historical summary.** Raw reports, generated files, and source copies
were removed from the current tree at the user's request. They remain
in commit `a9b8307`. File paths below refer to that saved state unless
they link to a file still in the current tree. These outputs are not
required to build the proofs or run the test tools.

Both cases are incomplete. The campaign runner returns 1.

- Length 32 reaches its 3,600-second limit: 27 completed paths, 32 partial
  paths, and no error witnesses.
- Length 64 is stopped with SIGINT at the user's pause request: 4 completed
  paths, 43 partial paths, and one solver-error report. This is incomplete
  evidence, not a production C counterexample or a passing check.

The manifest (`manifest.json`) records failed completion and exploration
checks. `archive.json` records 303 retained file hashes.
The archive includes bitcode, witnesses, statistics, source snapshots,
and logs. Source hashes were checked against the campaign manifest.
The process scan (`../pause-processes.json`) records no active verification
process after the stop. Resume only on user instruction, in a new output
directory.

The raw `.kquery` files remain local and are stored in Git through
`query-files.tar.gz`. `query-files.json` records the
compressed-file hash and each original-file hash. Every member was read
back from the compressed archive and checked against its original hash.
To restore the paths used by `archive.json`, run from this directory:

```sh
tar -xzf query-files.tar.gz
```
