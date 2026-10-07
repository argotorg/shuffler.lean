# Source mutation and metamorphic checks

Run from `spikes/clight-permute` in the pinned shell:

```sh
python3 tests/challenge/matrix.py
```

The actual extracted printer executable must already exist under
`build/project`; `build.sh` creates it. The matrix checks its fresh output
against the unchanged generated C before preparing variants.

The matrix creates nine changed C variants, five changed solc Permute
variants, and two behavior-preserving controls. Each variant has exactly
one source replacement. It changes a size/depth bound, destination rule,
equal-value rule, swap, trace, blocked position, or excess depth. The C++
variants alter only a copied `solc_permute.inc`. The original implementation
and upstream source remain unchanged.

`build/challenge/manifest.json` exposes each variant's source path, source
hash, original hash, and exact replacement for other test or verification
tools. `results.json` records compilation, linking, test outcome, and
witness paths separately. All source variants differ from canonical
generation, including the behavior-preserving controls. This byte check
tests source provenance; it does not prove or disprove semantic correctness.
No formal verifier is invoked by this matrix. No test failure is called a
proof. Compilation failure, native crash, or timeout does not count as a
successful behavioral witness in this matrix.

The test loads the actual compiled C function and upstream C++ oracle.
For 695 valid inputs, including exhaustive permutations and binary values
through length four, boundary cases through length 1024, and 200 seeded
random cases, it checks:

- Equality of status, final or partial data, complete trace, and error fields.
- Repeated calls with different initial work/output contents.
- Three bijective renamings of unsigned 32-bit value IDs: XOR, complement,
  and an odd affine map modulo 2^32. Equality is preserved; ordering can change.
- Exact replay of every trace, required success data, and blocked depth.
- Trailing buffer guards, unchanged unwritten trace tails, and the oracle's
  unchanged input permutation.

There are ten native calls per valid input. Empty, oversized, and malformed
permutation inputs are checked separately against the C rejection contract.
Each buffer starts at the first element of a separate unsigned array.
Trailing guards use extra valid capacity; the test does not pass a pointer
into the middle of an array. These guard checks detect writes outside the
active buffers. They do not detect every out-of-range read and are not a
replacement for the separate ASan, UBSan, and MSan runs.

The latest input is saved before each case, and a failed check records its
reason. This gives a replayable witness for each changed variant. The
fixed baseline and both behavior-preserving controls must pass the same
tests. Python optimization must remain disabled because the checks use
assertions.

New test code uses GPL-3.0-or-later. Solc notices remain on extracted and
modified copies. The matrix adds no CompCert or non-commercial dependency.
