{ pkgs }:
pkgs.vscode-with-extensions.override {
  vscode = pkgs.vscodium;
  vscodeExtensions = pkgs.vscode-utils.extensionsFromVscodeMarketplace [{
    name = "VSCoq";
    publisher = "maximedenes";
    version = "1.9.0";
    sha256 = "sha256-6S1Ykaz1lsxw+pTry6+ZzMH5QiFXvNkf3UU1aX7K83I=";
  }];
}
