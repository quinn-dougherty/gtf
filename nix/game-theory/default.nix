{ self, ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    with inputs';
    let
      doom-emacs = import ./emacs.nix { inherit pkgs nix-doom-emacs; };
      vscodium = import ./codium.nix { inherit pkgs; };
      shell = { text-editor ? [ ] }:
        import ./shell.nix { inherit pkgs text-editor; };
    in {
      devShells = {
        coq-no-ui = shell { };
        emacs = shell { text-editor = [ doom-emacs ]; };
        codium = shell { text-editor = [ vscodium ]; };
        coq = shell { text-editor = [ emacs vscodium ]; };
      };
      packages.coq-game-theory = pkgs.stdenv.mkDerivation {
        name = "game-theory-compile";
        inputsFrom = shell { };
        src = ../../game-theory;
        buildPhase = "dune build";
        installPhase = "mkdir -p $out";
      };
    };
}
