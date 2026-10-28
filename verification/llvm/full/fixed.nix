{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource,
  legacySource }:
let
  base = import ./validation.nix {
    inherit lib stdenvNoCC python3 llvm vellvm vellvmPkgs verifiedLLVM clightSource;
  };
in base.overrideAttrs (old: {
  pname = "shuffler-llvm-fixed-proofs";
  buildInputs = old.buildInputs ++ [
    vellvmPkgs.rocqPackages_9_1.mathcomp-boot
    vellvmPkgs.rocqPackages_9_1.mathcomp-fingroup
  ];
  buildPhase = ''
    runHook preBuild
    cd full
    sh prepare.sh "$PWD/candidate-build" ${clightSource}/permute.c
    cp candidate-build/*.v candidate-build/permute.ll .
    mkdir Legacy
    cp ${legacySource}/Permute.v Legacy/
    sed 's/^Require Import /From Legacy Require Import /' \
      ${legacySource}/Proofs.v > Legacy/Proofs.v
    for module in Permute ClightEval ClightEvalProofs ClightMemory ClightScalar \
      ClightLoop ClightInitialize ClightEntry ClightValidation ClightSwap \
      ClightExchangeSuccess ModelArrays ClightNormalize SolcModel ModelSpec \
      ModelProofs ClightCall ClightChoose ChooseModel ClightExchange PermuteSpec \
      ClightMain ClightSearch FirstFree ClightFill ClightFillLoop \
      ClightNormalization ClightCorrect; do
      cp ${clightSource}/$module.v .
    done
    python3 check_fixed.py ${verifiedLLVM}/proof/compcert \
      ${clightSource}/check-assumptions.py "$PWD/../import_ast.py"
    runHook postBuild
  '';
  postInstall = old.postInstall + ''
    cp -r Legacy "$out/proof/"
  '';
})
