{ lib, stdenvNoCC, stdenv, fetchFromGitHub, fetchurl, applyPatches, autoPatchelfHook,
  makeWrapper, gmp, zlib, python3, vellvmPkgs, tinyX86Patches ? [] }:
let
  coq = vellvmPkgs.coqPackages_9_1.coq;
  proofs = vellvmPkgs.coqPackages_9_1;
  proofTools = [ coq coq.ocamlPackages.ocaml coq.ocamlPackages.findlib ];
  commonInputs = [
    vellvmPkgs.rocqPackages_9_1.stdlib
    proofs.stdpp
    proofs.coq-record-update
  ];

  sailCompiler = stdenvNoCC.mkDerivation {
    pname = "sail-isa-compiler";
    version = "0.20.3";
    src = fetchurl {
      url = "https://github.com/rems-project/sail/releases/download/0.20.3-binary/sail-Linux-x86_64.tar.gz";
      hash = "sha256-jXzXViTs5AfXABrTKQWhOuER1cwaBVQE8hUQ4RMgfj8=";
    };
    nativeBuildInputs = [ autoPatchelfHook makeWrapper ];
    buildInputs = [ gmp zlib stdenv.cc.cc.lib ];
    dontConfigure = true;
    dontBuild = true;
    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      cp -r bin share doc LICENSE Z3_LICENSE THIRD_PARTY_FILES.md "$out/"
      wrapProgram "$out/bin/sail" \
        --set SAIL_DIR "$out/share/sail" \
        --prefix PATH : "$out/bin"
      runHook postInstall
    '';
    doInstallCheck = true;
    installCheckPhase = ''
      runHook preInstallCheck
      "$out/bin/sail" --version
      runHook postInstallCheck
    '';
    meta = {
      description = "Sail instruction-set specification compiler";
      homepage = "https://github.com/rems-project/sail";
      license = lib.licenses.bsd2;
      platforms = [ "x86_64-linux" ];
    };
  };

  mkProofLibrary = attrs: stdenvNoCC.mkDerivation ({
    nativeBuildInputs = proofTools;
    enableParallelBuilding = true;
    buildPhase = ''
      runHook preBuild
      make -f Makefile.coq -j "$NIX_BUILD_CORES"
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      make -f Makefile.coq install \
        COQLIBINSTALL="$out/lib/coq/${coq.coq-version}/user-contrib"
      mkdir -p "$out/share/doc/${attrs.pname}"
      cp LICENSE "$out/share/doc/${attrs.pname}/"
      runHook postInstall
    '';
    meta.license = lib.licenses.bsd2;
  } // attrs);

  sailStdpp = mkProofLibrary {
    pname = "rocq-sail-stdpp";
    version = "0.20.3-e7b914c";
    src = fetchFromGitHub {
      owner = "rems-project";
      repo = "coq-sail";
      rev = "e7b914cddc032e3676eebd87a808229828013e9c";
      hash = "sha256-SEac4aAYl2jMHEGMXdi/VjjXB89nS8FVB/UizcEnUPM=";
    };
    propagatedBuildInputs = commonInputs;
    configurePhase = ''
      runHook preConfigure
      coq_makefile -R src-stdpp SailStdpp src-stdpp/*.v -o Makefile.coq
      runHook postConfigure
    '';
  };

  tinyX86Source = applyPatches {
    name = "sail-tiny-x86-229bd84-source";
    src = fetchFromGitHub {
      owner = "rems-project";
      repo = "sail-tiny-x86";
      rev = "229bd8448937042baa51b0a2d14bc437929b0dce";
      hash = "sha256-EvdN0iZe+2Iaa7fp3Z1oCmYa8C3yY2lmqC908Kjz3U0=";
    };
    patches = tinyX86Patches;
  };

  tinyX86 = mkProofLibrary {
    pname = "rocq-sail-tiny-x86";
    version = "229bd84";
    src = tinyX86Source;
    nativeBuildInputs = proofTools ++ [ sailCompiler python3 ];
    propagatedBuildInputs = commonInputs ++ [ sailStdpp ];
    configurePhase = ''
      runHook preConfigure
      mkdir generated
      sail --strict-var --rocq --rocq-record-update \
        --rocq-output-dir generated -o Tiny_x86 $(cat sail_files)
      coq_makefile -R generated SailTinyX86 \
        generated/Tiny_x86_types.v generated/Tiny_x86.v -o Makefile.coq
      runHook postConfigure
    '';
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      python3 ${./test_semantics.py} ${sailCompiler}/bin/sail "$PWD" > semantics-tests.txt
      cat semantics-tests.txt
      runHook postCheck
    '';
    postInstall = ''
      cp semantics-tests.txt "$out/"
    '';
  };
in mkProofLibrary {
  pname = "rocq-archsem-x86";
  version = "078c405f";
  src = fetchFromGitHub {
    owner = "rems-project";
    repo = "archsem";
    rev = "078c405ffb7fb968dc7aa396d603b416a72b8481";
    hash = "sha256-6ltzhKCLVijUHgyEL0mNpnlt++e+1GDHDkxrZiPz29Q=";
  };
  patches = [ ./patches/archsem-adapter-module.patch ];
  propagatedBuildInputs = commonInputs ++ [
    proofs.equations proofs.coq-hammer-tactics sailStdpp tinyX86
  ];
  configurePhase = ''
    runHook preConfigure
    coq_makefile -R Common ASCommon -R ArchSem ArchSem -R ArchSemX86 ArchSemX86 \
      Common/*.v ArchSem/*.v ArchSemX86/*.v -o Makefile.coq
    runHook postConfigure
  '';
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    for test in X86SeqModelTest X86OperationalModelTest; do
      coqc -R Common ASCommon -R ArchSem ArchSem -R ArchSemX86 ArchSemX86 \
        "ArchSemX86/tests/$test.v"
    done
    coqchk -silent -o \
      -R Common ASCommon -R ArchSem ArchSem -R ArchSemX86 ArchSemX86 \
      ArchSemX86.X86Inst > kernel-check.txt 2> kernel-context.txt
    runHook postCheck
  '';
  postInstall = ''
    ln -s ${tinyX86Source} "$out/share/sail-tiny-x86"
    cp ${tinyX86}/semantics-tests.txt "$out/"
    cp kernel-check.txt kernel-context.txt "$out/"
  '';
  passthru = { inherit sailCompiler sailStdpp tinyX86 tinyX86Source; };
}
