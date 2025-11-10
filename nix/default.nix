{
  craneLib,
  self,
  system,
  pkgs,
}: {
  cargoMachete = import ./cargoMachete.nix {inherit craneLib pkgs;};
  cargoRefinedRust = import ./cargoRefinedRust.nix {inherit craneLib self system pkgs;};

  mkDepRocqDerivation = import ./mkDepRocqDerivation.nix {inherit pkgs;};

  overlays = {
    ocamlFlambda = import ./ocamlFlambdaOverlay.nix {inherit pkgs;};
  };
}
