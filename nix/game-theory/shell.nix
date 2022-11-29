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
    pkgs.nodejs
  ];
  #  python-environment = let
  #    mach = mach-nix.lib.${pkgs.system}.mkPython {
  #      requirements = "alectryon==1.4.0";
  #      # ignoreDataOutdated = true; # needed for some error
  #    };
  #  in [ mach ];
  python = [ pkgs.python310Packages.alectryon ];
in pkgs.mkShell {
  name = "game-theory-development";
  buildInputs = builtins.concatLists [ base-shell-inputs text-editor python ];
}
