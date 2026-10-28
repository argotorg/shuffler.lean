args@{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource }:
(import ./prefix.nix args).overrideAttrs (_: {
  pname = "shuffler-llvm-validation-proofs";
  src = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../Normalize.v ../import_ast.py
      (lib.fileset.fileFilter (file:
        file.hasExt "v" || file.hasExt "py" || file.name == "prepare.sh" ||
        file.name == "kernel-axioms.txt" || file.name == "kernel-axioms-clight.txt") ./.)
    ];
  };
  buildPhase = ''
    runHook preBuild
    cd full
    sh prepare.sh "$PWD/candidate-build" ${clightSource}/permute.c
    cp candidate-build/*.v candidate-build/permute.ll .
    for module in Permute ClightEval ClightEvalProofs ClightMemory ClightScalar \
      ClightLoop ClightInitialize ClightEntry ClightValidation; do
      cp ${clightSource}/$module.v .
    done
    python3 check_validation.py ${verifiedLLVM}/proof/compcert \
      ${clightSource}/check-assumptions.py "$PWD/../import_ast.py"
    runHook postBuild
  '';
  postInstall = ''
    cp kernel-axioms-clight.txt "$out/"
  '';
})
