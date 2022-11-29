{ pkgs }:
pkgs.vscode-with-extensions.override {
  vscode = pkgs.vscodium;
  vscodeExtensions = pkgs.vscode-utils.extensionsFromVscodeMarketplace [{
    name = "VSCoq";
    publisher = "maximedenes";
    version = "0.3.6";
    sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
  }];
}
