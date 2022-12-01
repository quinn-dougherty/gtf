{ self, withSystem, ... }:
let hciSystem = "x86_64-linux";
in {
  flake = withSystem hciSystem ({ config, effects, pkgs, inputs', ... }: {
    ciSystems = [ hciSystem ];
    onPush = let packages = self.packages.${hciSystem};
    in {
      checks.outputs = self.checks.${hciSystem}.lint;
      coq-game-theory.outputs = packages.coq-game-theory;
      nashwires.outputs = packages.nashwires;
      development.outputs = self.devShells.${hciSystem};
      comms = {
        outputs = { agent-signature = packages.agent-signature; };
        effects = {
          agent-signature = effects.mkEffect {
            effectScript =
              "putStateFile agent-signature.pdf ${packages.agent-signature}/agent-signature.pdf";
          };
        };
      };
    };
  });
}
