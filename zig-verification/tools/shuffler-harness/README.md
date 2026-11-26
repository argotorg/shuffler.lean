# Native harness of the Zig shuffle (K3b)

Calls the compiled `solidity_shuffler_shuffle` natively and records inputs and outputs as JSON lines.

    python3 -I tools/shuffler-harness/native.py gen [OUTDIR]   # default Lift/Shuffler/Test/data, about 10 s
    python3 -I tools/shuffler-harness/native.py selfcheck      # about 30 s

Needs zig 0.17.1 (`ZIG`, default `zig` on PATH) and `gcc`.
Build in `/tmp/shuffler-harness` (`SHUFFLER_WORK`): the compile command of `Lift/LLVM/data/shuffler/src/README.md`
gives `shuffler.s`, which must equal the committed `shuffler.s`; `gcc -shared -nostdlib` links it. No download.

Files: `native-random.jsonl` (random-*), `native-boundary.jsonl`, `native-big.jsonl` (sizes 1,024 and 1,025).
`native-status2.jsonl` (class `status2-spill`: status 2 with a changed spill byte) is made by `status2.py`:
`python3 -I tools/shuffler-harness/status2.py gen` (about 1 minute, no Zig: it links the committed `shuffler.s`);
trial i uses `random.Random("20261119:status2-spill:<i>")`; the first 30 hits are the vectors; the header has the trials.
Line 1 of each file is the header: seed, SHA-256 of `shuffler.zig`, the commit that last changed it, SHA-256 of `shuffler.s`.
Seed: `SEED` = 20261119; case i of class c uses `random.Random("<SEED>:<c>:<i>")`. Each case runs with a zero
workspace and with a random one (random record padding too); the script stops if the results differ.

Input fields: `source`, `target`: lists of u64 words (the slot `payload | kind << 32 | opcode << 40 | padding << 48`);
`spills`: bytes, one for each variable id (length of the spill buffer); `reach`: u64; `allowed`: bool.
Words in `source[0 .. source_size)`, `target[0 .. target_size)`. Also `id` (`class/index`) and `class`.

Output fields: `status` (0 done, 1 blocked, 2 assertion failure); `spills_after` (the spill buffer after the call, for each
status). Only for status 0: `stack`: `target_size` u64 words, padding included; `trace`: list of `[kind, depth, slot word]`
(the 2 padding bytes of an op are not recorded); `sources`: `target_size` entries, a source offset or `null` (the word
`2^64 - 1`).

Self-check: reruns the 720 random inputs; reach 1 gives status 2 for each; reach 2, flipped spilling and a reversed target
each change the output of at least one input; regenerates the three files and compares them byte for byte with the committed ones.
