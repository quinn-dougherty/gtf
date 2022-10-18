{
  description = "Game Theory Foundations - executable textbook";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.05";
    nixpkgs-unstable.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-doom-emacs = {
      url = "github:nix-community/nix-doom-emacs";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, nixpkgs-unstable, nix-doom-emacs, flake-utils }:
    let
      overlays = [ ];
      coq-packages = pkgs: with pkgs.coqPackages;
        [ pkgs.ocaml pkgs.dune_3 coq paco mathcomp mathcomp-analysis ];
      base-shell = { pkgs, text-editor }: pkgs.mkShell {
        name = "gametheory-foundations-devShell";
        buildInputs = (coq-packages pkgs) ++ text-editor;
      };
      emacs = system: {
        nix-doom-emacs.package.${system}.doomPrivateDir = ./nix/doom.d;
      };
      codium = pkgs: pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscodium;
          vscodeExtensions = pkgs.vscode-utils.extensionsFromVscodeMarketplace [
            {
              name = "VSCoq";
              publisher = "maximedenes";
              version = "0.3.6";
              sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
            }
          ];
      };
      development = pkgs: let
          doom = emacs { system = pkgs.system; };
          vscodium = codium { inherit pkgs; };
        in flake-utils.lib.flattenTree {
          default = base-shell {
            inherit pkgs;
            text-editor = [ doom vscodium ];
          };
          just-emacs = base-shell {
            inherit pkgs;
            text-editor = [ doom ];
          };
          just-codium = base-shell {
            inherit pkgs;
            text-editor = [ vscodium ];
          };
          no-editors = base-shell {
            inherit pkgs;
            text-editor = [ ];
          };
        };
      builds = pkgs: flake-utils.lib.flattenTree {
        default = pkgs.stdenv.mkDerivation {
            name = "gametheory-foundations-compile";
            buildInputs = coq-packages pkgs;
            buildPhase = ''
              dune build
            '';
            installPhase = ''
              mkdir -p $out
            '';
          };
      };
      localFlakeOutputs = { pkgs, ... }: {
        devShells = development pkgs;
        packages = builds pkgs;
      };
      herc = let
        hci-system = "x86_64-linux";
        hci-pkgs = import nixpkgs { system = hci-system; overlays = overlays; };
        hci-shells = development hci-pkgs;
        hci-builds = builds hci-pkgs;
      in {
        herculesCI = {
          ciSystems = [ hci-system ];
          onPush = {
            texteditors.outputs = hci-shells;
            gtf.outputs = hci-builds;
          };
        };
      };
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = overlays;
        };
        pkgs-unstable = import nixpkgs-unstable {
          inherit system;
          overlays = overlays;
        };
      in localFlakeOutputs pkgs) // herc;

}
