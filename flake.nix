{
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
    flake-utils.url = "github:numtide/flake-utils";
    systems.url = "github:nix-systems/default";
  };

  outputs = inputs:
  inputs.flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import inputs.nixpkgs { inherit system; }; in
    {
      # clang and AFL++ for the fuzzer builds in Fuzz/
      devShells.default = pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } {
        buildInputs = [ pkgs.elan pkgs.cmake pkgs.ninja pkgs.boost pkgs.fmt pkgs.nlohmann_json pkgs.range-v3 pkgs.aflplusplus ];
      };
    });
}
