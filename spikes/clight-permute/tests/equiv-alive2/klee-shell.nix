# SPDX-License-Identifier: GPL-3.0-or-later
let
  lock = builtins.fromJSON (builtins.readFile ../../../../flake.lock);
  pin = lock.nodes.nixpkgs.locked;
  pkgs = import (builtins.fetchTarball { url = pin.url; sha256 = pin.narHash; }) {
    config.allowUnfree = false;
  };
  # This revision tests LLVM 19 in upstream CI. The older packaged KLEE 3.2
  # predates that support and is marked broken in this pinned Nixpkgs.
  klee = pkgs.klee.overrideAttrs (old: {
    version = "git-9a36a6782b814fe1fa37439652b875114faa0e20";
    src = pkgs.fetchzip {
      url = "https://github.com/klee/klee/archive/9a36a6782b814fe1fa37439652b875114faa0e20.tar.gz";
      hash = "sha256-ZftUYugRlpKOhCwEaZmEETredZ4nm3AOldf95JNgWRQ=";
    };
    patches = [];
    cmakeFlags = old.cmakeFlags ++ [
      "-DENABLE_KLEE_ASSERTS=ON"
      "-DENABLE_UNIT_TESTS=OFF"
      "-DENABLE_SYSTEM_TESTS=OFF"
    ];
    doCheck = false;
    meta = old.meta // { broken = false; };
  });
in pkgs.mkShell {
  packages = [ klee pkgs.llvmPackages_19.clang pkgs.llvmPackages_19.llvm
    pkgs.python3 pkgs.range-v3 pkgs.z3 ];
}
