{ self, withSystem, lib, ... }:
let
  hciSystem = "x86_64-linux";
  packages = self.packages.${hciSystem};
  comms-documents = (import ./lib.nix { inherit lib; }).dirNames ./../comms;
in {
  herculesCI = { config, ... }:
    withSystem hciSystem ({ hci-effects, ... }:
      let
        run-condition = config.repo.branch == "main";
        documentEffectForAll = let
          documentEffectFor = document: {
            name = document;
            value = hci-effects.runIf run-condition (hci-effects.mkEffect {
              effectScript = "putStateFile ${document}.pdf ${
                  packages.${document}
                }/${document}.pdf";
            });
          };
        in documents: builtins.listToAttrs (map documentEffectFor documents);
        soupaultDeploy = hci-effects.netlifyDeploy {
          content = packages.soupault;
          productionDeployment = run-condition;
          secretName = "default-netlify";
          siteId = "b982a29f-501a-43ac-8702-3800e8e22cf5";
        };
      in {
        ciSystems = [ hciSystem ];
        onPush = {
          # default.enable = false; # odd that this isn't working; https://flake.parts/options/hercules-ci-effects.html#opt-herculesCI.onPush
          checks.outputs = self.checks.${hciSystem}.lint;
          coq-game-theory.outputs = packages.coq-game-theory;
          nashwires.outputs = packages.nashwires;
          development.outputs = self.devShells.${hciSystem};
          comms.outputs.effects = documentEffectForAll comms-documents;
          soupault.outputs.effects = soupaultDeploy;
        };
      });
}
