{ self, ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      nodejs14 = pkgs.nodejs-14_x;
      nodeDependencies = (pkgs.callPackage ./npm.nix {
        inherit pkgs;
        system = pkgs.system;
        nodejs = nodejs14;
      }).nodeDependencies;
    in {
      packages.nashwires = pkgs.stdenv.mkDerivation {
        name = "nashwires-build";
        src = ./../../nashwires;
        buildInputs = [ nodejs14 ];
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
