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
      verified-llvm = pkgs.callPackage ./verification/llvm {
        inherit llvm vellvm vellvmPkgs;
        clightSource = ./spikes/clight-permute;
      };
      llvm-memory = pkgs.callPackage ./verification/llvm/full {
        inherit vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
      };
      llvm-prefix = pkgs.callPackage ./verification/llvm/full/prefix.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
      };
      llvm-validation = pkgs.callPackage ./verification/llvm/full/validation.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
      };
      llvm-fixed = pkgs.callPackage ./verification/llvm/full/fixed.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
        legacySource = ./spikes/rocq-permute;
      };
      llvm-normalization = pkgs.callPackage ./verification/llvm/full/normalization.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
        legacySource = ./spikes/rocq-permute;
      };
      llvm-choice = pkgs.callPackage ./verification/llvm/full/choice.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
        legacySource = ./spikes/rocq-permute;
      };
      llvm-main = pkgs.callPackage ./verification/llvm/full/main.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
        legacySource = ./spikes/rocq-permute;
      };
      llvm-call = pkgs.callPackage ./verification/llvm/full/call.nix {
        inherit llvm vellvm vellvmPkgs;
        verifiedLLVM = verified-llvm;
        clightSource = ./spikes/clight-permute;
        legacySource = ./spikes/rocq-permute;
      };
    in
    {
      packages.vellvm = vellvm;
      packages.verified-llvm = verified-llvm;
      packages.verified-permute-llvm = llvm-call;
      checks.verified-llvm = verified-llvm;
      checks.llvm-memory = llvm-memory;
      checks.llvm-prefix = llvm-prefix;
      checks.llvm-validation = llvm-validation;
      checks.llvm-fixed = llvm-fixed;
      checks.llvm-normalization = llvm-normalization;
      checks.llvm-choice = llvm-choice;
      checks.llvm-main = llvm-main;
      checks.llvm-call = llvm-call;
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
      devShells.default = pkgs.mkShell {
        buildInputs = [ pkgs.elan ];
      };
    });
}
