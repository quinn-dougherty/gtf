{ lib }: {
  dirNames = folder:
    let
      ls = builtins.readDir folder;
      keepDirs = key: value: value == "directory";
    in lib.mapAttrsToList (key: value: key) (lib.filterAttrs keepDirs ls);
}
