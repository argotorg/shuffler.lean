# SPDX-License-Identifier: GPL-3.0-or-later
let
  lock = builtins.fromJSON (builtins.readFile ../../../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  pkgs = import (builtins.fetchTarball { url = pin.url; sha256 = pin.narHash; }) {
    system = builtins.currentSystem;
    config.allowUnfree = false;
  };
in pkgs.mkShell {
  packages = [ pkgs.frama-c pkgs.why3 pkgs.z3 pkgs.cvc5 pkgs.python3 ];
}
