{ pkgs, text-editor }:
let coq-packages = import ./coq.nix { inherit pkgs; };
in pkgs.mkShell {
  name = "coq-game-theory-development";
  buildInputs = coq-packages ++ text-editor;
}
