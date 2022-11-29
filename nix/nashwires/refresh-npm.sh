#!/usr/bin/env sh

# Must be ran from `cd ./nix/nashwires`

node2nix --development --input ../../nashwires/package.json --lock ../../nashwires/package-lock.json --composition ./npm.nix
