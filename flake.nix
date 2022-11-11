{
  description = "Game Theory Foundations - executable textbook";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.05";
    nixpkgs-unstable.url = "nixpkgs/nixos-unstable";
    mach-nix = {
      url = "mach-nix/3.5.0";
      inputs.nixpkgs.follows = "nixpkgs-unstable";
    };
    flake-utils.url = "github:numtide/flake-utils";
    nix-doom-emacs = {
      url = "github:nix-community/nix-doom-emacs";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, nixpkgs-unstable, mach-nix, nix-doom-emacs, flake-utils }:
    let
      overlays = [ ];
      base-shell-inputs = pkgs:
        with pkgs.coqPackages; [
          # To build
          pkgs.ocaml
          pkgs.dune_3
          coq
          # Coq dependencies
          paco
          ITree
          mathcomp
          mathcomp-analysis
          # For website
          serapi
          pkgs.nodejs
        ];
      python-environment = system: let
        mach = mach-nix.lib.${system}.mkPython {
          requirements = "alectryon==1.4.0";
          ignoreDataOutdated = true;  # needed for some error
        };
        in [ mach ];
      base-shell = { pkgs, text-editor }:
        pkgs.mkShell {
          name = "gametheory-foundations-development";
          buildInputs = builtins.concatLists [
            (base-shell-inputs pkgs)
            text-editor
            (python-environment pkgs.system)
          ];
        };
      emacs-make = system: nix-doom-emacs.package.${system} { doomPrivateDir = ./nix/doom.d; };
      codium-make = pkgs:
        pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscodium;
          vscodeExtensions =
            pkgs.vscode-utils.extensionsFromVscodeMarketplace [{
              name = "VSCoq";
              publisher = "maximedenes";
              version = "0.3.6";
              sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
            }];
        };
      development = pkgs:
        let
          doom = emacs-make { system = pkgs.system; };
          vscodium = codium-make { inherit pkgs; };
        in flake-utils.lib.flattenTree {
          default = base-shell {
            inherit pkgs;
            text-editor = [ ];
          };
          just-emacs = base-shell {
            inherit pkgs;
            text-editor = [ doom ];
          };
          just-codium = base-shell {
            inherit pkgs;
            text-editor = [ vscodium ];
          };
          both-editors = base-shell {
            inherit pkgs;
            text-editor = [ doom vscodium ];
          };
        };
      builds = pkgs:
        flake-utils.lib.flattenTree {
          default = pkgs.stdenv.mkDerivation {
            name = "gametheory-foundations-compile";
            buildInputs = base-shell-inputs pkgs;
            src = ./.;
            buildPhase = ''
              dune build
            '';
            installPhase = ''
              mkdir -p $out
            '';
          };
        };
      checks = pkgs:
        flake-utils.lib.flattenTree {
          default = pkgs.stdenv.mkDerivation {
            name = "gtf-lint";
            buildInputs = with pkgs; [ nixfmt nodePackages.prettier ];
            src = ./.;
            buildPhase = ''
              nixfmt --check flake.nix
              prettier --check .
            '';
            installPhase = ''
              mkdir -p $out
            '';
          };
        };
      localFlakeOutputs = { pkgs, ... }: {
        devShells = development pkgs;
        packages = builds pkgs;
        checks = checks pkgs;
      };
      herc = let
        hci-system = "x86_64-linux";
        hci-pkgs = import nixpkgs {
          system = hci-system;
          overlays = overlays;
        };
        hci-shells = development hci-pkgs;
        hci-builds = builds hci-pkgs;
        hci-checks = checks hci-pkgs;
      in {
        herculesCI = {
          ciSystems = [ hci-system ];
          onPush = {
            texteditors.outputs = hci-shells;
            gtf.outputs = hci-builds;
            lint.outputs = hci-checks;
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
