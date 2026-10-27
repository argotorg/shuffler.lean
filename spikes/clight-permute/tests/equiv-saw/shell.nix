# SPDX-License-Identifier: GPL-3.0-or-later
let
  lock = builtins.fromJSON (builtins.readFile ../../../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  pkgs = import (builtins.fetchTarball {
    url = pin.url;
    sha256 = pin.narHash;
  }) { system = builtins.currentSystem; config.allowUnfree = false; };
  # Use the distribution without bundled solver executables. Both solvers
  # come from explicit Nix dependencies. SAW 1.5 supports LLVM through version 20.
  saw = pkgs.saw-tools.overrideAttrs (_: {
    src = pkgs.fetchurl {
      url = "https://github.com/GaloisInc/saw-script/releases/download/v1.5/saw-1.5-ubuntu-22.04-X64.tar.gz";
      hash = "sha256-yooryByu5gbwPsU4sPXPKZ6kVxtlqYElU7Ffs30BSCY=";
    };
  });
in pkgs.mkShell {
  packages = [ saw pkgs.z3 pkgs.yices pkgs.llvmPackages_20.clang
    pkgs.llvmPackages_20.llvm pkgs.range-v3 pkgs.python3 pkgs.binutils ];
}
