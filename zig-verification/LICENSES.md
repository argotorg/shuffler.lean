# Source notices and license status

This review package retains the existing source notices. It does not assign a
new license to code whose owner has not selected one.

| Source | Notice |
| --- | --- |
| Zig shuffler source in `Lift/LLVM/data/shuffler/src/shuffler.zig` | GPL-3.0 SPDX header; license text in the same directory as `LICENSE.txt` |
| Required Kraken snapshot in `vendor/Kraken` | MIT; see `vendor/Kraken/LICENSE` |
| Loogle snapshot in `vendor/loogle` | Apache-2.0; see `vendor/loogle/LICENSE` |
| Local verification and harness code | The source repository has no root license file; the owner must select terms for publication |
| Parent `shuffler.lean` repository | No root license file was present at the recorded base |

The assembly is built from the included GPL-3.0 Zig source. Preserve its source
and license notices when distributing the package. Existing per-file notices
also apply. Resolve the license for the new contribution before public release.
