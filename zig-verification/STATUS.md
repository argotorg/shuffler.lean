# Partial proof status

This is a source export from the paused campaign of 2026-11-25. It is not a
completed proof of the shuffler.

The journal had 707 closed rows out of 769, with 62 open rows. It had 21 closed
function finals out of 31. These are historical campaign counts, not the result
of a new campaign in this package. The default build checks the 21 included
final proofs at their exact contract types. It does not replay the 769-row run.

The following ten final contracts remain open:

- `emissionBuildBottomUp`
- `emissionGenerate`
- `emissionPermute`
- `emissionPermuteAtLowestHeight`
- `emissionProduce`
- `emissionRemoveSurplus`
- `emissionRun`
- `plannerResolve`
- `plannerRun`
- `shuffle`

The included `Review/Contracts.lean` imports contract declarations for all 31
functions. `Review/Closed.lean` lists the 21 checked final proofs. Proposed
internal contracts are model-generated statements retained for review. Their
names and ledger do not make them trusted claims about the intended algorithm.
The top-level `ShuffleStatement` remains a review input; its proof is open.

The closed finals refine the compiled machine code to their stated contracts.
They do not prove full composition, the final shuffle result, or a correspondence
between the Zig model and upstream's high-level algorithm model. Those claims
remain separate proof tasks.

No partial working proof attempts, paid traces, account budgets, or frozen
worker originals are included. Source hashes and the closed-final inventory are
in `SOURCE-MANIFEST.json`.

Two harness fixes tested in the source workspace's recovery tree were not
installed in the running source at the pause. They concern budget admission and
the type check of generated output maps. They are excluded from this export.
The package therefore does not claim to contain those fixes. Review of generated
maps and failed proof admissions remains part of the unfinished work.
