{ pkgs }:
with pkgs.coqPackages; [
  pkgs.ocaml
  pkgs.dune_3
  coq
  paco
  ITree
  mathcomp
  mathcomp-analysis
  serapi
]
