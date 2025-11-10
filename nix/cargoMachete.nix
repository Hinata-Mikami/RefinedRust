{
  craneLib,
  pkgs,
}: {
  pname,
  src,
}:
craneLib.mkCargoDerivation {
  inherit pname src;

  buildPhaseCargoCommand = "cargo machete";
  nativeBuildInputs = with pkgs; [cargo-machete];

  cargoArtifacts = null;
  doInstallCargoArtifacts = false;
  pnameSuffix = "-machete";
}
