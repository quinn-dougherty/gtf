{ self, ... }:
let hciSystem = "x86_64-linux";
in {
  flake.herculesCI = {
    ciSystems = [ hciSystem ];
    onPush = {
      checks.outputs = self.checks.${hciSystem}.lint;
      coq-game-theory.outputs = self.packages.${hciSystem}.coq-game-theory;
      nashwires.outputs = self.packages.${hciSystem}.nashwires;
      development.outputs = self.devShells.${hciSystem};
    };
  };
}
