{ lib, ... }:
let
  comms-documents =
    (import ./../lib.nix { inherit lib; }).dirNames ./../../comms;
in {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      tex-pkgs = with pkgs; [
        pandoc
        (texlive.combine {
          inherit (texlive) scheme-small thmtools datetime xpatch fmtcount;
        })
      ];
      util = import ./util.nix {
        inherit tex-pkgs;
        mkDerivation = pkgs.stdenv.mkDerivation;
      };
    in {
      devShells.pandoc = pkgs.mkShell {
        name = "comms-development";
        buildInputs = tex-pkgs;
      };
      packages = util.documentForAll comms-documents;
    };
}
