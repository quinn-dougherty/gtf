{ pkgs, text-editor }:
let
  coq-packages = with pkgs.coqPackages; [
    pkgs.ocaml
    pkgs.dune_3
    coq
    paco
    ITree
    mathcomp
    mathcomp-analysis
    serapi
  ];
in pkgs.mkShell {
  name = "coq-game-theory-development";
  buildInputs = coq-packages ++ text-editor;
}
