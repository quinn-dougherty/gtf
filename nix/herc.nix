{ self, withSystem, lib, ... }:
let
  hciSystem = "x86_64-linux";
  packages = self.packages.${hciSystem};
  comms-documents = (import ./lib.nix { inherit lib; }).dirNames ./../comms;
in {
  herculesCI = withSystem hciSystem ({ hci-effects, branch, ... }:
    let
      run-condition = branch: branch == "main";
      documentEffectForAll = branch:
        let
          documentEffectFor = document: {
            name = document;
            value = hci-effects.runIf (run-condition branch)
              (hci-effects.mkEffect {
                effectScript = "putStateFile ${document}.pdf ${
                    packages.${document}
                  }/${document}.pdf";
              });
          };
        in documents: builtins.listToAttrs (map documentEffectFor documents);
      soupaultDeploy = branch:
        hci-effects.netlifyDeploy {
          content = packages.soupault;
          productionDeployment = run-condition branch;
          secretName = "default-netlify";
          siteId = "b982a29f-501a-43ac-8702-3800e8e22cf5";
        };
    in {
      ciSystems = [ hciSystem ];
      onPush = {
        checks.outputs = self.checks.${hciSystem}.lint;
        coq-game-theory.outputs = packages.coq-game-theory;
        nashwires.outputs = packages.nashwires;
        development.outputs = self.devShells.${hciSystem};
        comms.outputs.effects = documentEffectForAll branch comms-documents;
        soupault.outputs.effects = soupaultDeploy branch;
      };
    });
}
