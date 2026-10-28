{ lib, stdenvNoCC, python3, vellvm, vellvmPkgs, verifiedLLVM, clightSource }:
stdenvNoCC.mkDerivation {
  pname = "shuffler-llvm-memory-proofs";
  version = "0.1.0";
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.unions [
      ./MemoryRelation.v ./WordMemory.v ./CellRelation.v ./MemoryTests.v
      ./Control.v ./Instructions.v
      ./check.py ./kernel-axioms.txt
    ];
  };
  nativeBuildInputs = [ vellvmPkgs.coqPackages_9_1.coq python3 ];
  buildInputs = [ vellvm vellvmPkgs.rocqPackages_9_1.stdlib ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    python3 check.py ${verifiedLLVM}/proof/compcert \
      ${clightSource}/check-assumptions.py
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/proof"
    cp ./*.v ./*.vo "$out/proof/"
    cp assumptions.txt kernel-context.txt kernel-axioms.txt "$out/"
    runHook postInstall
  '';
}
