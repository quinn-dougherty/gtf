{ self, withSystem, ... }:
let
  hciSystem = "x86_64-linux";
  packages = self.packages.${hciSystem};
in {
  herculesCI = withSystem hciSystem ({ config, effects, pkgs, inputs', ... }: {
    ciSystems = [ hciSystem ];
    onPush = {
      checks.outputs = self.checks.${hciSystem}.lint;
      coq-game-theory.outputs = packages.coq-game-theory;
      nashwires.outputs = packages.nashwires;
      development.outputs = self.devShells.${hciSystem};
      comms.outputs = { agent-signature = packages.agent-signature; };
    };
    effects = let packages = self.packages.${hciSystem};
    in {
      agent-signature = effects.mkEffect {
        effectScript =
          "putStateFile agent-signature.pdf ${packages.agent-signature}/agent-signature.pdf";

      };
    };
  });
}
