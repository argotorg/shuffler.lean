{ lib, stdenvNoCC, python3, llvm, archsemX86, llvmCall }:
stdenvNoCC.mkDerivation {
  pname = "shuffler-x86-codegen-probe";
  version = "0.1.0";
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.unions [
      ./probe_codegen.py ./test_codegen_probe.py ./permute.S
    ];
  };
  nativeBuildInputs = [ python3 llvm.clang llvm.llvm archsemX86.sailCompiler ];
  dontConfigure = true;
  dontFixup = true;
  buildPhase = ''
    runHook preBuild
    python3 test_codegen_probe.py > probe-tests.txt 2>&1
    cat probe-tests.txt
    python3 probe_codegen.py \
      ${llvmCall}/permute.proved.ll \
      ${archsemX86.tinyX86Source} \
      ${archsemX86.sailCompiler}/bin/sail "$PWD/build"
    cp probe-tests.txt build/
    cp ${archsemX86.tinyX86Source}/LICENSE build/model/
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -r build/. "$out/"
    runHook postInstall
  '';
  meta = {
    description = "Compiler output and Sail decoder coverage for permute";
    license = lib.licenses.gpl3Plus;
    platforms = [ "x86_64-linux" ];
  };
}
