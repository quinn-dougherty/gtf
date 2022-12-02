#!/usr/bin/env sh

# This script is only relevant if you're rolling nixos.

# We need to patchelf rescript executables. https://github.com/NixOS/nixpkgs/issues/107375

# node2nix works best with nodejs-14
set -x

fhsShellName="nashwires-fhs-development"
fhsShellDotNix="{pkgs ? import <nixpkgs> {} }: (pkgs.buildFHSUserEnv { name = \"${fhsShellName}\"; targetPkgs = pkgs: with pkgs; [nodejs-14_x]; runScript = \"npm install\"; }).env"
nix-shell - <<<"$fhsShellDotNix"

theLd=$(patchelf --print-interpreter $(which mkdir))
patchelf --set-interpreter $theLd ./node_modules/rescript/linux/*.exe
theSo=$(find /nix/store/*$fhsShellName*/lib64 -name libstdc++.so.6 | head -n 1)
patchelf --replace-needed libstdc++.so.6 $theSo ./node_modules/rescript/linux/ninja.exe