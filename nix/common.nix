{ ... }:

{
  perSystem = { config, self', inputs', pkgs, ... }:
    with pkgs;
    let lintDeps = [ nixfmt nodePackages.prettier ];
    in {
      devShells.default = with pkgs;
        mkShell {
          name = "gtf-development";
          buildInputs = builtins.concatLists [
            lintDeps
            [ node2nix nodePackages.npm-check-updates ]
            self'.devShells.coq.buildInputs
            self'.devShells.pandoc.buildInputs
            self'.devShells.soupault.buildInputs
            self'.packages.nashwires.buildInputs
          ];
        };
      checks.lint = pkgs.stdenv.mkDerivation {
        name = "gtf-lint";
        buildInputs = lintDeps;
        src = ./../.;
        buildPhase = ''
          for nixfile in $(find $src -type f | grep '[.].nix')
          do
            nixfmt --check $nixfile
          done
          prettier --check $src --ignore-path .gitignore
        '';
        installPhase = "mkdir -p $out";
      };
    };
}
