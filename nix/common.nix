{ ... }:

{
  perSystem = { config, self', inputs', pkgs, ... }: {
    devShells.default = with pkgs;
      mkShell {
        name = "gtf-development";
        buildInputs = builtins.concatLists [
          [ node2nix nixfmt nodePackages.prettier ]
          self'.devShells.coq-no-ui.buildInputs
          self'.devShells.pandoc.buildInputs
          [ soupault ]
        ];
      };
    checks.lint = pkgs.stdenv.mkDerivation {
      name = "gtf-lint";
      buildInputs = with pkgs; [ nixfmt nodePackages.prettier ];
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
