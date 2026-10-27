<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Proof check evidence

The saved `check-proofs.sh` run passed on 2026-10-06. It checked all 62
project, legacy, and allowed CompCert modules with `coqchk`. The source
copies in `build/proofs` match the committed project proof sources.
`sources.sha256` records the proof, printer, C, and dependency-manifest
bytes. Its paths are relative to the repository root.

`assumptions.txt` records `Print Assumptions` output for each named
theorem, lemma, and example. The full-call theorem uses upstream axioms
and semantic parameters; this is not an axiom-free development. See
[LICENSING.md](../LICENSING.md#trust-is-separate-from-licensing).

To repeat the check from the repository root:

```sh
nix develop --impure --expr 'import ./spikes/clight-permute/shell.nix' \
  --command sh spikes/clight-permute/check-proofs.sh
```

The saved log contains paths from the execution environment. Those paths
are evidence of that run, not required locations for a new build.
