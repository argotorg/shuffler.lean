<!-- SPDX-License-Identifier: GPL-3.0-or-later -->

# Frama-C proof tools

The proof shell uses the repository's pinned Nixpkgs and sets
`config.allowUnfree = false`. It selects Frama-C, Why3, Z3, CVC5, and Python.
It does not select Alt-Ergo. The proof runner limits Why3 prover detection to
a directory that contains only Z3 and CVC5. It uses a local Why3 configuration.

| Component | Installed version | License evidence |
| --- | --- | --- |
| Frama-C | 33.0 (Arsenic) | Installed `share/doc/frama-c/LICENSE`: most source is LGPL-2.1; it also lists BSD, CC0, CDDL, OCaml linking-exception, and QPL components. Documentation is CC-BY-SA-4.0. |
| Why3 | 1.8.2 | Installed `share/why3/LICENSE`: LGPL-2.1 with a linking exception; `extmap` files use the OCaml LGPL-2 license. |
| Z3 | 4.16.0 | Pinned Nixpkgs package metadata: MIT. |
| CVC5 | 1.3.4 | Pinned Nixpkgs binary metadata: GPL-3.0-only. `cvc5 --version` identifies the CVC5 source as modified BSD, plus LGPLv3 GMP/LibPoly and the CaDiCaL/SymFPU libraries. |
| Python | 3.14.7 | Pinned Nixpkgs package metadata: Python-2.0. |

Why3's top-level license has a warning that some GUI icon sets may prohibit
commercial use. The installed image tree was checked separately. It contains
the Why3 logo and the FatCow icon set. The FatCow notice states CC-BY-3.0,
which permits commercial use. There is no other installed icon set in this
package. Do not infer that the generic top-level warning permits use of any
other Why3 version or optional icon set.

The checked executable store paths are:

- `/nix/store/16fk4776m9icn2awjr3z21ag0ymy28pj-frama-c-33.0`
- `/nix/store/2qc0qa6n76scgri4v1lq9payv13diwmy-why3-1.8.2`
- `/nix/store/rx0qkfh4zcf1lp9i94kq04yh149w10a1-z3-4.16.0`
- `/nix/store/p396cicn1h7sglnx0ywhl22c9fff8x9g-cvc5-1.3.4`

The closure from `nix-store -qR` is retained in
`build/frama-c/closure.txt`. It contains no Alt-Ergo package. Package license
metadata is retained in `build/frama-c/package-licenses.json`. This is a
package and installed-notice audit, not a review of every source file in the
transitive tool closure. The shell rejects packages which the pinned Nixpkgs
marks as unfree.

The added CVC5 closure, metadata, and full version/license text are retained
in `cvc5-closure.txt`, `cvc5-license.json`, and `cvc5-version.txt` under that
same result directory. Its closure also contains no Alt-Ergo package.

The local annotations, scripts, and tests use GPL-3.0-or-later. They do not
copy CompCert's restricted compiler or printer code. The source-C checker does
not invoke CompCert or `clightgen`. Its input is the C file from this project's
printer. The existing separate CompCert source allowlist still applies to the
Rocq/Clight proof.
