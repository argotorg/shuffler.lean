{ lib, stdenvNoCC, python3, llvm, vellvm, vellvmPkgs, archsemX86,
  verifiedLLVM, llvmCall, clightSource }:
let
  coq = vellvmPkgs.coqPackages_9_1.coq;
in stdenvNoCC.mkDerivation {
  pname = "shuffler-x86-proofs";
  version = "0.1.0";
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.fileFilter (file:
      file.hasExt "v" || builtins.elem file.name [
        "check.py" "test_check.py" "generate_program.py" "test_program.py" "test_proofs.py"
        "permute.S" "kernel-axioms.txt" "BUILD.md"
      ]) ./.;
  };
  nativeBuildInputs = [
    coq coq.ocamlPackages.ocaml coq.ocamlPackages.findlib python3 llvm.clang llvm.llvm
  ];
  buildInputs = [
    archsemX86 vellvm vellvmPkgs.rocqPackages_9_1.stdlib
    vellvmPkgs.rocqPackages_9_1.mathcomp-boot
    vellvmPkgs.rocqPackages_9_1.mathcomp-fingroup
  ];
  dontConfigure = true;
  dontStrip = true;
  buildPhase = ''
    runHook preBuild
    python3 test_check.py > checker-tests.txt 2>&1
    cat checker-tests.txt
    python3 check.py ${verifiedLLVM}/proof/compcert ${llvmCall}/proof \
      ${clightSource}/check-assumptions.py "$PWD/build"
    cp checker-tests.txt build/
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/proof" "$out/logs"
    cp build/proof/*.v build/proof/*.vo "$out/proof/"
    cp build/*.txt build/permute.o build/permute.bin "$out/"
    cp build/*.log "$out/logs/"
    cp -r build/mutations "$out/"
    cp check.py test_check.py generate_program.py test_program.py test_proofs.py permute.S \
      kernel-axioms.txt "$out/proof/"
    cp BUILD.md "$out/"
    runHook postInstall
  '';
  passthru = { inherit llvmCall verifiedLLVM archsemX86; };
  meta = {
    description = "Rocq proofs for the shuffler x86 instruction and memory model";
    license = lib.licenses.gpl3Plus;
    platforms = [ "x86_64-linux" ];
  };
}
