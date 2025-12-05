{
  crane,
  pkgs,
  rrPkgs,
}: let
  craneLib = crane.mkLib pkgs;
in {
  inherit (craneLib) cargoDeny overrideToolchain;

  cargoClippy = devToolchain: craneLib.cargoClippy.override {clippy = devToolchain;};
  cargoFmt = devToolchain: craneLib.cargoFmt.override {rustfmt = devToolchain;};
  cargoMachete = import ./cargoMachete.nix {inherit craneLib pkgs;};
  cargoRefinedRust = import ./cargoRefinedRust.nix {inherit craneLib rrPkgs pkgs;};
}
