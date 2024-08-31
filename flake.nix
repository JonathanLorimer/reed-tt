{
  description = "reed-tt";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    with flake-utils.lib;
      eachDefaultSystem (system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        agda = pkgs.agda.withPackages (p: [
          p.standard-library
        ]);
      in {
        # nix develop
        devShell = pkgs.mkShell {
          buildInputs = [
            agda
          ];
        };
      });
}
