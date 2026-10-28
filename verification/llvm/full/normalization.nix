args@{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource,
  legacySource }:
(import ./fixed.nix args).overrideAttrs (old: {
  pname = "shuffler-llvm-normalization-proofs";
  buildPhase = builtins.replaceStrings
    [ "python3 check_fixed.py" ] [ "python3 check_normalization.py" ] old.buildPhase;
})
