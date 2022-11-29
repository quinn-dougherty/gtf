{
  description = "Game Theory Foundations - executable textbook";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    nix-doom-emacs = {
      url = "github:nix-community/nix-doom-emacs";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-parts, nix-doom-emacs }@inputs:
    flake-parts.lib.mkFlake { inherit self; } {
      imports = [ ./nix/nashwires ./nix/game-theory ./nix ];
      systems = [ "x86_64-linux" ]; # "aarch64-darwin" ];
    };
}
