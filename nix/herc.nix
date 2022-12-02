{ self, withSystem, ... }:
let
  hciSystem = "x86_64-linux";
  packages = self.packages.${hciSystem};
in {
  herculesCI = withSystem hciSystem ({ hci-effects, ... }: {
    ciSystems = [ hciSystem ];
    onPush = {
      checks.outputs = self.checks.${hciSystem}.lint;
      coq-game-theory.outputs = packages.coq-game-theory;
      nashwires.outputs = packages.nashwires;
      development.outputs = self.devShells.${hciSystem};
      comms.outputs.effects = {
        agent-signature = hci-effects.mkEffect {
          effectScript =
            "putStateFile agent-signature.pdf ${packages.agent-signature}/agent-signature.pdf";
        };
      };
    };
  });
}
