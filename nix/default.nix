{
  craneLib,
  pkgs,
}: {
  cargoMachete = import ./cargoMachete.nix {inherit craneLib pkgs;};
  mkDepRocqDerivation = import ./mkDepRocqDerivation.nix {inherit pkgs;};

  overlays = {
    ocamlFlambda = import ./ocamlFlambdaOverlay.nix {inherit pkgs;};
  };
}
