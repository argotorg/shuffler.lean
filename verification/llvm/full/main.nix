args@{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource,
  legacySource }:
(import ./choice.nix args).overrideAttrs (old: {
  pname = "shuffler-llvm-main-proofs";
  buildPhase = builtins.replaceStrings
    [ "python3 check_choice.py" ] [ "python3 check_main.py" ] old.buildPhase;
})
