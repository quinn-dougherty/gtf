#!/usr/bin/env sh

# Must be ran from `cd ./nix/nashwires`

node2nix -i ../../nashwires/package.json -l ../../nashwires/package-lock.json -18 -c ./npm.nix
