{
  pkgs,
  rust-overlay,
}:
components:
with pkgs.lib;
let
  toolchain = rust-overlay.lib._internal.defaultManifests.nightly.latest.pkg;
  getArch = pkg: attrNames toolchain.${pkg}.target;
  desiredComponents = remove "rust-src" components;
in
if desiredComponents == [ ] then
  [ ]
else
  foldl' intersectLists (getArch (head desiredComponents)) (map getArch (tail desiredComponents))
