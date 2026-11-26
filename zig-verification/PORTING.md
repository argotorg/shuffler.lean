# Source export and package changes

The upstream base is `argotorg/shuffler.lean` main at
`c8ddfa5978eef078a462d9dc9fd876baa9806e1c`. Its root Lake package, toolchain,
and C++ source pin are unchanged. This addition uses a separate Lake package.

`SOURCE-MANIFEST.json` records the source workspace commit, the fact that the
workspace was dirty, the original SHA-256 of each copied file, the 21 final
contracts, the paused journal counts, and the exact Solidity source identity.
Those original hashes are provenance, not hashes of files after adaptation.
`PACKAGE-MANIFEST.json` records the final exported file hashes separately.
Use `validation/axioms.json` for the full axiom names from the export check.
The original final-proof inventory can use shortened axiom names.

The export starts from the closed finals and the tool/test entry points, then
follows source imports. It excludes denied hand proofs. It retains required
runtime fixtures, generic generation and scheduling code, recovery code, worker
validation, terminal views, and the worker primer. It excludes source-repository
history, accounts, daemon state, caches, model replies, and campaign attempts.

The port makes these changes:

- Adds the independent package, proof-contract wrappers, source checks,
  generation audit, validation tests, documentation, and CI.
- Runs the generation audit in four batches with a 120-second limit per batch.
  The single-process audit exceeded that limit. The combined receipt requires
  all 31 functions and rejects repeated or incomplete batches.
- Replaces the worker's Git Loogle dependency with the included source snapshot.
  Lake manifests use local paths for Kraken, leantools, and Loogle.
- Sets the local worker search roots to this package and `vendor/Kraken`.
- Adds a worker wrapper that sets this package's root and Loogle binary and
  removes inherited Lean search paths. It cannot select another project through
  an inherited `LEANTOOLS_ROOT`.
- Records `lake exe skel` in full and level-report command metadata, without
  requiring the source workspace's Nix shell.
- Replaces `.kraken/Kraken` paths in the worker primer with `vendor/Kraken/Kraken`.
- Uses `zig` from PATH, or `ZIG`, in the optional native harness. It reads the
  Solidity commit from the source manifest. The native fixture headers use
  that same source commit; their input and output cases are unchanged.
- Adds a separate Solidity source submodule for the Zig revision. It does not
  change the existing C++ oracle submodule.
- Changes the legacy D15 endpoint configuration to inactive placeholders and
  removes a host-specific path from its Zig type fixture. Includes the Python
  dependencies of the legacy benchmark shell scripts and keeps executable modes.
- Includes the worker's `garbage.lrat` negative-test fixture and all four native
  harness fixtures. Import-only source scans do not find these runtime inputs.

Accepted generated proof source is copied without proof edits. No contract is
weakened to make the export build. Unused references in old module comments can
name design documents that are not part of this package.

The vendored Kraken directory is the required source closure of a local snapshot
with no Git metadata. It differs from the Kraken revision on upstream's
`kraken-bbu` branch. Its per-file bytes, not a guessed public commit, identify it.
The Loogle files were compared directly with the local Git blobs at
`9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0`. Regular file bytes match that
revision. Two test-fixture toolchain symlinks are copied as files with their
resolved contents. Their resolved source hashes are in `SOURCE-MANIFEST.json`.
The Loogle license and source notices are retained.

The nine model files in `Lift/Shuffler/Ext` match the copies on upstream
`kraken-bbu` at `adb2285bc2d7c6b57620cf62121c41798c904929`, after the documented
import rename. They retain the `FlatShuffler` namespace. Their presence does not
prove a correspondence theorem for the Zig model.
