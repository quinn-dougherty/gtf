# Game Theory Foundations - executable textbook WIP
[![Hercules-ci][Herc badge]][Herc link]
[![Cachix Cache][Cachix badge]][Cachix link]

[Herc badge]: https://img.shields.io/badge/Herc-CI-yellowgreen?style=plastic&logo=nixos
[Herc link]: https://hercules-ci.com/github/quinn-dougherty/gtf
[Cachix badge]: https://img.shields.io/badge/Cachix-effective--altruism-blueviolet?style=plastic&logo=nixos
[Cachix link]: https://effective-altruism.cachix.org

The name is inspired by the mighty executable textbook volumes known as Software Foundations. 

Idk how much time I'll be putting into this. I'm just figuring out what abstractions and libraries I want to use. 

## Level

It's a lot to pick up if its your first exposure to coq. 

## To play

Install `nix` and enable flakes. 

My package manager/build script can create a build of `emacs` or `vscodium` that comes with `coq` installed, enabled, and has the dependencies. This is isolated, it won't interfere with your home `emacs`/`codium` build and won't interfere with any other `coq` installs you have on your system. A `.opam` file is included in case you don't want to use `nix` (or you're a `windows` user), but I'm not planning on using it (if you figure it out, do send a PR to this `README.md`). `macos` users: please let me know how things go with nix! Linux users: if you install `cachix` and run `cachix use effective-altruism` you're liable to get some cache hits, saving build time.

```sh
nix develop .#just-emacs # downloads coq and libraries, just builds emacs
nix develop .#just-codium # downloads coq and libraries, just builds codium
nix develop .#no-editors # downloads coq and libraries
nix develop # downloads coq and libraries, builds both emacs and codium. 
```

Editors are put onto `$PATH`, so launch them from terminal like `emacs --fullscreen` or `codium`

### with `direnv` and `nix-direnv` 

```sh
echo "use flake" > .envrc
direnv allow
```

`direnv`/`nix-direnv` has excellent synergy with `emacs`, it's how I manage `coq` installations. 

### Compile

After you've chosen a `nix develop` command, run `dune build`. 

You will run `dune build` at the top level every time you get to the bottom of a file and move onto the next one. 
