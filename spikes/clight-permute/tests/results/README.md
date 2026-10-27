<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Verification run summaries

The dated campaigns keep their summaries here:

- [Resumed checks](resumed-2026-10-06/README.md).
- [Extended checks](extended-2026-10-06/README.md).
- [Frama-C component proofs](frama-c-2026-10-07/README.md).

Raw logs, solver reports, generated programs, copied sources, and archives
from these campaigns were removed from the current tree at the user's
request. The proof and test tools do not read these result directories.
New runs write their outputs under the ignored `spikes/clight-permute/build/`
directory. Keep summaries in Git; keep raw outputs outside the review diff.

The removed files remain in commit `a9b8307`. For example, read a report with:

```sh
git show a9b8307:spikes/clight-permute/tests/results/resumed-2026-10-06/frama-memory-summary.json
```

This cleanup reduces the branch diff. It does not remove files from Git
history or reduce the size of existing Git objects. The summaries record
past results; they do not replace the original reports for a full audit.
