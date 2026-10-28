{ lib, stdenv, python3, llvm, vellvm, vellvmPkgs, clightSource }:
let
  rocq = vellvmPkgs.coqPackages_9_1.coq;
in stdenv.mkDerivation {
  pname = "shuffler-verified-llvm";
  version = "0.1.0";
  # The full-call memory proofs have a separate check. Changes there do not
  # change the scalar module or its proof and export tests.
  src = lib.cleanSourceWith {
    src = ./.;
    filter = path: type: baseNameOf path != "full";
  };
  nativeBuildInputs = [
    rocq python3 llvm.clang llvm.llvm
    vellvmPkgs.ocaml-ng.ocamlPackages_4_14.ocaml
  ];
  buildInputs = [ vellvm vellvmPkgs.rocqPackages_9_1.stdlib ];
  dontConfigure = true;
  dontStrip = true;
  hardeningDisable = [ "fortify" ];
  inherit clightSource;
  buildPhase = ''
    runHook preBuild
    sh build.sh
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -r artifacts/. "$out/"
    runHook postInstall
  '';
}
