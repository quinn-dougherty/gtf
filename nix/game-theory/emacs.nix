{ pkgs, nix-doom-emacs }:
nix-doom-emacs.package.${pkgs.system} { doomPrivateDir = ./../doom.d; }
