# `game-theory-foundations`

## Level

It's a lot to pick up if its your first exposure to `coq`, since I use `mathcomp-analysis`.

## To play

Install `nix` and enable flakes.

My package manager/build script can create a build of `emacs` or `vscodium` that comes with `coq` installed, enabled, and has the dependencies. This is isolated, it won't interfere with your home `emacs`/`codium` build and won't interfere with any other `coq` installs you have on your system. A `.opam` file is included in case you don't want to use `nix` (or you're a `windows` user), but I'm not planning on using it (if you figure it out, do send a PR to this `README.md`). `macos` users: please let me know how things go with nix! Linux users: if you install `cachix` and run `cachix use effective-altruism` you're liable to get some cache hits, saving build time.

```sh
# The flake is currently busted, this documents the intended UX, not the current UX!
nix develop .#coq-emacs   # downloads coq and libraries, just builds emacs
nix develop .#coq-codium  # downloads coq and libraries, just builds codium
nix develop .#coq # downloads coq and libraries, builds both emacs and codium.
nix develop .#coq-no-ui # downloads coq and libraries with no text editor builds
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
