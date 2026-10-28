{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, verifiedLLVM, clightSource }:
stdenvNoCC.mkDerivation {
  pname = "shuffler-llvm-prefix-proofs";
  version = "0.1.0";
  src = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../Normalize.v ../import_ast.py
      ./MemoryRelation.v ./WordMemory.v ./CellRelation.v ./MemoryTests.v
      ./Control.v ./Instructions.v ./Entry.v ./Index.v ./Initialize.v ./Prefix.v
      ./candidate ./prepare.sh ./check.py ./check_prefix.py ./kernel-axioms.txt
    ];
  };
  nativeBuildInputs = [ vellvmPkgs.coqPackages_9_1.coq python3 llvm.clang llvm.llvm ];
  buildInputs = [ vellvm vellvmPkgs.rocqPackages_9_1.stdlib ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    cd full
    sh prepare.sh "$PWD/candidate-build" ${clightSource}/permute.c
    cp candidate-build/*.v candidate-build/permute.ll .
    python3 check_prefix.py ${verifiedLLVM}/proof/compcert \
      ${clightSource}/check-assumptions.py "$PWD/../import_ast.py"
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/proof"
    cp ./*.v ./*.vo "$out/proof/"
    cp permute.ll assumptions.txt kernel-context.txt kernel-axioms.txt mutations.txt "$out/"
    cp -r mutations "$out/"
    runHook postInstall
  '';
}
