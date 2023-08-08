#!/usr/bin/env sh

# Must be ran from `cd ./nix/nashwires`

# pushd ../../nashwires
# npm update
# popd

node2nix --development --input ../../nashwires/package.json --lock ../../nashwires/package-lock.json --composition ./npm.nix --nodejs-18
