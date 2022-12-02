{ self, withSystem, lib, ... }:
let
  hciSystem = "x86_64-linux";
  packages = self.packages.${hciSystem};
  comms-documents = (import ./lib.nix { inherit lib; }).dirNames ./../comms;
in {
  herculesCI = withSystem hciSystem ({ hci-effects, ... }:
    let
      util = let
        documentEffectFor = document: {
          name = document;
          value = hci-effects.mkEffect {
            effectScript = "putStateFile ${document}.pdf ${
                packages.${document}
              }/${document}.pdf";
          };
        };
      in {
        documentEffectForAll = documents:
          builtins.listToAttrs (map documentEffectFor documents);
        soupaultDeploy = branch:
          hci-effects.netlifyDeploy {
            content = packages.soupault;
            productionDeployment = (branch == "main");
            secretName = "netlify";
            siteId = "9d17ad40-c2f8-4933-b7d8-bb0ac30f0907";
          };
      };
    in {
      ciSystems = [ hciSystem ];
      onPush = {
        checks.outputs = self.checks.${hciSystem}.lint;
        coq-game-theory.outputs = packages.coq-game-theory;
        nashwires.outputs = packages.nashwires;
        development.outputs = self.devShells.${hciSystem};
        comms.outputs.effects = util.documentEffectForAll comms-documents;
        soupault.outputs.effects = util.soupaultDeploy;
      };
    });
}
