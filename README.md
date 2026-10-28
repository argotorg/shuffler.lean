# shuffler-lean

This repo contains a work in progress formalization of the new plan based shuffler in solc.

## Development

Either run `nix develop` or install [elan](https://github.com/leanprover/elan).

Then run `lake build` to compile the project.

Run `lake build Tests` to check the proofs and regression tests.

The [Clight-to-LLVM proof](verification/llvm/README.md) builds on PR #6.
Run `nix build .#verified-llvm` to check the scalar call proof and export its LLVM.
