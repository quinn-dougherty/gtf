{ pkgs, text-editor }:
let
  base-shell-inputs = with pkgs.coqPackages; [
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
    pkgs.nodejs-14_x
  ];
  python = [ pkgs.python310Packages.alectryon ];
in pkgs.mkShell {
  name = "game-theory-development";
  buildInputs = builtins.concatLists [ base-shell-inputs text-editor python ];
}
