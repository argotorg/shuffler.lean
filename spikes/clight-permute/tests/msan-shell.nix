# SPDX-License-Identifier: GPL-3.0-or-later
let
  lock = builtins.fromJSON (builtins.readFile ../../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  source = builtins.fetchTarball { url = pin.url; sha256 = pin.narHash; };
  pkgs = import source {
    system = builtins.currentSystem;
    config.allowUnfree = false;
  };
  llvmSource = pkgs.fetchFromGitHub {
    owner = "llvm";
    repo = "llvm-project";
    rev = "llvmorg-21.1.8";
    hash = "sha256-pgd8g9Yfvp7abjCCKSmIn1smAROjqtfZaJkaUkBSKW0=";
  };
in pkgs.mkShell {
  packages = [ pkgs.clang pkgs.llvmPackages.llvm pkgs.cmake pkgs.ninja
               pkgs.python3 pkgs.range-v3 pkgs.curl ];
  MSAN_LLVM_SOURCE = llvmSource;
}
