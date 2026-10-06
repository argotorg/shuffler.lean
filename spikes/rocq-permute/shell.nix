# SPDX-License-Identifier: GPL-3.0-or-later
let
  # Read the lock directly: getFlake on a worktree can bind its Git narHash.
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  source = builtins.fetchTarball { url = pin.url; sha256 = pin.narHash; };
  pkgs = import source {
    system = builtins.currentSystem;
    config.allowUnfree = false;
  };
in pkgs.mkShell {
  packages = [
    pkgs.coq
    pkgs.coqPackages.stdlib
    pkgs.coqPackages.mathcomp-ssreflect
    pkgs.coqPackages.mathcomp-fingroup
  ];
}
