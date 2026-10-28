args@{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource,
  legacySource }:
(import ./main.nix args).overrideAttrs (old: {
  pname = "shuffler-llvm-call-proofs";
  src = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../Normalize.v ../import_ast.py
      (lib.fileset.fileFilter (file:
        file.hasExt "v" || file.hasExt "py" || file.name == "prepare.sh" ||
        file.name == "export.sh" || file.name == "print_full.ml" ||
        file.name == "kernel-axioms.txt" || file.name == "kernel-axioms-clight.txt") ./.)
    ];
  };
  nativeBuildInputs = old.nativeBuildInputs ++ [
    vellvmPkgs.ocaml-ng.ocamlPackages_4_14.ocaml
  ];
  dontStrip = true;
  buildPhase = builtins.replaceStrings
    [ "python3 check_main.py" "runHook postBuild" ]
    [ "python3 check_call.py" ''
      sh export.sh ${verifiedLLVM}/proof/compcert -Q . ""
      python3 test_export.py "$PWD" ${clightSource}/permute.c > export-tests.txt
      cat export-tests.txt
      runHook postBuild
    '' ] old.buildPhase;
  postInstall = old.postInstall + ''
    cp permute.proved.ll permute.proved.bc permute.proved.o export-tests.txt "$out/"
  '';
})
