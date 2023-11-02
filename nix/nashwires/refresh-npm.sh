#!/usr/bin/env sh

# Must be ran from `cd ./nix/nashwires`

pushd ../../nashwires
ncu -u
npm update --save --lockfile-version 2
rm -rf node_modules
popd

node2nix --development --input ../../nashwires/package.json --lock ../../nashwires/package-lock.json --composition ./npm.nix --nodejs-18
