{ pkgs, nix-doom-emacs }:
nix-doom-emacs.override { doomPrivateDir = ./../doom.d; }
