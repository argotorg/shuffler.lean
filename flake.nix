{
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
    flake-utils.url = "github:numtide/flake-utils";
    systems.url = "github:nix-systems/default";
    vellvm.url = "github:vellvm/vellvm/4c6db50077cbc0df3fb3156c0570129201cc35f3";
  };

  outputs = inputs:
  inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      llvm = pkgs.llvmPackages_20;
      vellvm = inputs.vellvm.packages.${system}.default;
      vellvmPkgs = import inputs.vellvm.inputs.nixpkgs { inherit system; };
      clightSource = builtins.path {
        path = ./spikes/clight-permute;
        name = "clight-permute-source";
      };
      legacySource = builtins.path {
        path = ./spikes/rocq-permute;
        name = "rocq-permute-source";
      };
      archsem-x86 = pkgs.callPackage ./verification/x86/archsem.nix {
        inherit vellvmPkgs;
        tinyX86Patches = [
          ./verification/x86/patches/tiny-x86-flags.patch
          ./verification/x86/patches/tiny-x86-jump.patch
        ];
      };
      verified-llvm = pkgs.callPackage ./verification/llvm {
        inherit llvm vellvm vellvmPkgs;
        inherit clightSource;
      };
      llvm-memory = pkgs.callPackage ./verification/llvm/full {
        inherit vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource;
      };
      llvm-prefix = pkgs.callPackage ./verification/llvm/full/prefix.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource;
      };
      llvm-validation = pkgs.callPackage ./verification/llvm/full/validation.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource;
      };
      llvm-fixed = pkgs.callPackage ./verification/llvm/full/fixed.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource legacySource;
      };
      llvm-normalization = pkgs.callPackage ./verification/llvm/full/normalization.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource legacySource;
      };
      llvm-choice = pkgs.callPackage ./verification/llvm/full/choice.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource legacySource;
      };
      llvm-main = pkgs.callPackage ./verification/llvm/full/main.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource legacySource;
      };
      llvm-call = pkgs.callPackage ./verification/llvm/full/call.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        inherit clightSource legacySource;
      };
      x86-proofs = pkgs.callPackage ./verification/x86 {
        inherit llvm vellvm vellvmPkgs;
        archsemX86 = archsem-x86;
        verifiedLLVM = verified-llvm;
        llvmCall = llvm-call;
        inherit clightSource;
      };
      x86-codegen-probe = pkgs.callPackage ./verification/x86/codegen.nix {
        inherit llvm;
        archsemX86 = archsem-x86;
        llvmCall = llvm-call;
      };
    in
    {
      packages.vellvm = vellvm;
      packages.verified-llvm = verified-llvm;
      packages.verified-permute-llvm = llvm-call;
      packages.archsem-x86 = archsem-x86;
      packages.x86-proofs = x86-proofs;
      packages.x86-codegen-probe = x86-codegen-probe;
      checks.verified-llvm = verified-llvm;
      checks.llvm-memory = llvm-memory;
      checks.llvm-prefix = llvm-prefix;
      checks.llvm-validation = llvm-validation;
      checks.llvm-fixed = llvm-fixed;
      checks.llvm-normalization = llvm-normalization;
      checks.llvm-choice = llvm-choice;
      checks.llvm-main = llvm-main;
      checks.llvm-call = llvm-call;
      checks.archsem-x86 = archsem-x86;
      checks.x86-proofs = x86-proofs;
      checks.x86-codegen-probe = x86-codegen-probe;
      devShells.verified-llvm = pkgs.mkShell {
        inputsFrom = [ verified-llvm ];
      };
      devShells.full-llvm = pkgs.mkShell {
        inputsFrom = [ verified-llvm ];
        packages = [
          vellvmPkgs.rocqPackages_9_1.mathcomp-boot
          vellvmPkgs.rocqPackages_9_1.mathcomp-fingroup
        ];
      };
      devShells.x86-equiv = pkgs.mkShell {
        inputsFrom = [ verified-llvm archsem-x86 ];
        packages = [
          archsem-x86 archsem-x86.sailCompiler
          vellvmPkgs.rocqPackages_9_1.mathcomp-boot
          vellvmPkgs.rocqPackages_9_1.mathcomp-fingroup
        ];
      };
      devShells.default = pkgs.mkShell {
        buildInputs = [ pkgs.elan ];
      };
    });
}
