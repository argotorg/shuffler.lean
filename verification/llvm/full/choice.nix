args@{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource,
  legacySource }:
(import ./normalization.nix args).overrideAttrs (old: {
  pname = "shuffler-llvm-choice-proofs";
  buildPhase = builtins.replaceStrings
    [ "python3 check_normalization.py" ] [ "python3 check_choice.py" ] old.buildPhase;
})
