{ self, ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      nodeDependencies =
        (pkgs.callPackage ./npm.nix { inherit pkgs; }).nodeDependencies;
    in {
      packages.nashwires = pkgs.stdenv.mkDerivation {
        name = "nashwires-compile-test";
        src = ../nashwires;
        buildInputs = [ pkgs.nodejs ];
        buildPhase = ''
          ln -s ${nodeDependencies}/lib/node_modules ./node_modules
          export PATH="${nodeDependencies}/bin:$PATH"

          # Build the distribution bundle in "dist"
          npm run build
          npm run test
        '';
        installPhase = ''
          mkdir -p $out
        '';
      };
    };
}
