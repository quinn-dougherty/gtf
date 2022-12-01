{ pkgs, text-editor }:
let
  for-coq = with pkgs.coqPackages; [
    pkgs.ocaml
    pkgs.dune_3
    coq
    paco
    ITree
    mathcomp
    mathcomp-analysis
  ];
  for-web = with pkgs; [
    nodejs
    coqPackages.serapi
    python310Packages.alectryon
  ];
in pkgs.mkShell {
  name = "game-theory-development";
  buildInputs = builtins.concatLists [ for-coq text-editor for-web ];
}
