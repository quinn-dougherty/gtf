{ ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      coq-gt = self'.packages.coq-game-theory;
      soupault-inputs = [
        pkgs.soupault
        pkgs.coqPackages.serapi
        pkgs.python310Packages.alectryon
      ];
    in {
      devShells.soupault = pkgs.mkShell {
        name = "gtf-soupault-development";
        buildInputs = soupault-inputs ++ self'.devShells.coq-no-ui.buildInputs;
      };
      packages.soupault = pkgs.stdenv.mkDerivation {
        name = "gtf-soupault";
        buildInputs = soupault-inputs ++ self'.devShells.coq-no-ui.buildInputs;
        src = ./../../soupault;
        configurePhase = ''
          cp -r ${coq-gt}/default/theories site
          chmod -R +rw site/**
        '';
        buildPhase = ''
          soupault
          soupault  # smelly but yeah it basically works.
        '';
        installPhase = ''
          mkdir -p $out
          cp -r build/* $out
        '';
      };
    };
}
