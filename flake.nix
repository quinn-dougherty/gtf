{
  description = "Game Theory Foundations - executable textbook";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    nix-doom-emacs = {
      url = "github:nix-community/nix-doom-emacs";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    hercules-ci-effects = {
      url = "github:hercules-ci/hercules-ci-effects";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self, nixpkgs, flake-parts, nix-doom-emacs, hercules-ci-effects }@inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        hercules-ci-effects.flakeModule
        ./nix/soupault
        ./nix/game-theory
        ./nix/comms
        ./nix/herc.nix
        ./nix/common.nix
      ];
      systems =
        [ "aarch64-linux" "aarch64-darwin" "x86_64-darwin" "x86_64-linux" ];
      hercules-ci.flake-update = {
        enable = true;
        when.dayOfMonth = 1;
        autoMergeMethod = "merge";
      };
    };
}
