<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Proof workflow controls

These checks test the proof workflow. Start a review with the
[core definitions and public statements](../../../../docs/verified-permute/README.md).

`ProofContract.v` fixes the expanded complete-call theorem type.
`ReachabilityContract.v` states the depth and value condition directly.
`PublicContract.v` checks that the readable public theorem supplies the
expanded call contract. The normal `check-proofs.sh` build checks all three.

`guards.py` changes the actual `ClightCorrect.permute_call_correct` theorem
in an isolated copy. Its controls include a baseline, an admission, a false
axiom, a shadowed axiom name, unsafe recursion, unsafe positivity, an
impossible precondition, and a `True` postcondition. Compilation and
`coqchk` are expected to accept these terms. The assumption/context policy
or the independent public type must reject each false or weakened claim.
The baseline must pass all checks.

`run.py` applies the source mutations in `mutations.json`. It first requires
the changed source to compile. The dependent proofs must reject each
behavior change. Both equivalent controls must retain the proofs and all
three public type fixtures. A timeout or source compilation error is not
a successful negative test. A proof-script failure alone is not a concrete
behavioral witness.

Run in the parent spike's Nix shell, after `check-proofs.sh` finishes:

```sh
python3 spikes/clight-permute/tests/proof-challenge/guards.py \
  --output spikes/clight-permute/build/proof-challenge/new-guards
python3 spikes/clight-permute/tests/proof-challenge/run.py \
  --output spikes/clight-permute/build/proof-challenge/new-mutations
```

Use a new output directory to retain prior evidence. Do not rebuild the
shared baseline while a control copies it. `--cases` selects named guard
controls; repeated `--only` options select source mutations.

The checks do not prove the printer correct. The separate
[uninitialized-read reproduction](../equiv-saw/undef-copy/README.md) shows
why accepted Clight execution alone is insufficient for the printed C.
