{ tex-pkgs, mkDerivation }:
let
  install = document: ''
    mkdir -p $out
    cp main.pdf $out/${document}.pdf
  '';
  build = ''
    pandoc \
      --from markdown+citations \
      --to latex \
      --out main.pdf \
      --pdf-engine xelatex \
      main.md
  '';
  documentFor = document: {
    name = document;
    value = mkDerivation {
      name = document;
      src = ./../../comms + "/${document}";
      buildInputs = tex-pkgs;
      buildPhase = build;
      installPhase = install document;
    };
  };
in {
  documentForAll = documents: builtins.listToAttrs (map documentFor documents);
}
