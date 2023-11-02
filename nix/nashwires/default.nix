{ self, ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      nodejs = pkgs.nodejs-18_x;
      nodeDependencies = (pkgs.callPackage ./npm.nix {
        inherit pkgs nodejs;
        system = pkgs.system;
      }).nodeDependencies;
    in {
      packages.nashwires = pkgs.stdenv.mkDerivation {
        name = "nashwires-build";
        src = ./../../nashwires;
        buildInputs = [ nodejs ];
        configurePhase = ''
          cp -r ${nodeDependencies}/lib/node_modules .
          export PATH="${nodeDependencies}/bin:$PATH"
        '';
        buildPhase = ''
          npm run build
        '';
        installPhase = ''
          mkdir -p $out
          # cp -r build $out
        '';
      };
    };
}
