{ self, ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      nodeDependencies = (pkgs.callPackage ./npm.nix {
        inherit pkgs;
        system = pkgs.system;
        nodejs = pkgs.nodejs-14_x;
      }).nodeDependencies;
    in {
      packages.nashwires = pkgs.stdenv.mkDerivation {
        name = "nashwires-compile-test";
        src = ./../../nashwires;
        buildInputs = [ pkgs.nodejs-14_x ];
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
