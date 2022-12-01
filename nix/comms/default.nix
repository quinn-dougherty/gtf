{ ... }: {
  perSystem = { config, self', inputs', pkgs, ... }:
    let
      tex-pkgs = with pkgs; [
        pandoc
        (texlive.combine {
          inherit (texlive) scheme-small thmtools datetime xpatch fmtcount;
        })
      ];
    in {
      devShells.pandoc = pkgs.mkShell {
        name = "comms-development";
        buildInputs = tex-pkgs;
      };
      packages = {
        agent-signature = pkgs.stdenv.mkDerivation {
          name = "riffing on the agent type";
          buildInputs = tex-pkgs;
          src = ./../../comms/agency-signature;
          buildPhase = ''
            pandoc \
              --from markdown+citations \
              --to latex \
              --out main.pdf \
              --pdf-engine xelatex \
              main.md
          '';
          installPhase = ''
            mkdir -p $out
            cp main.pdf $out/agent-signature.pdf
          '';
        };
      };
    };
}
