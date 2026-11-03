# SPDX-License-Identifier: GPL-3.0-or-later
let
  lock = builtins.fromJSON (builtins.readFile ../../../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  pkgs = import (builtins.fetchTarball { url = pin.url; sha256 = pin.narHash; }) {
    config.allowUnfree = false;
  };
in pkgs.mkShell {
  packages = [ pkgs.alive2 pkgs.clang pkgs.llvm pkgs.python3 pkgs.range-v3 ];
}
