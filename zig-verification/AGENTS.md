# Work in this package

Use the pinned toolchain from this directory. Read README.md, STATUS.md, and
KRAKEN.md before proof work. The full proof remains open.

Do not change an accepted contract, definition, or frozen worker original to
make a proof pass. Do not add axioms or use native_decide. Run the axiom gate.
Keep checkSeconds at most 180 and maxHeartbeats at most 400000. Use two Lean
threads and bound local checks. Do not run paid calls unless the user asks.

Use local/generation for the generation audit. A full dry run can write proof
modules; use a separate checkout for that work. Keep credentials, budgets,
transcripts, daemon state, and build products out of version control.
