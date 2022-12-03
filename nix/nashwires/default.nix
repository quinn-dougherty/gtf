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
        name = "nashwires-compile-test";
        src = ./../../nashwires;
        buildInputs = [ nodejs14 ];
        configurePhase = ''
          cp -r ${nodeDependencies}/lib/node_modules .
          export PATH="${nodeDependencies}/bin:$PATH"
          chmod -R +w node_modules/{rescript-mocha,rescript-fast-check}
        '';
        buildPhase = ''
          npm run build:peggy
          npm run build:rescript
          npm run test
        '';
        installPhase = ''
          mkdir -p $out
          cp -r lib $out
        '';
      };
    };
}
