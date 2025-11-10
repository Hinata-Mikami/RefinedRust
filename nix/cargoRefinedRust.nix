{
  craneLib,
  self,
  system,
  pkgs,
}: {
  cargoArtifacts,
  pname,
  src,
}:
craneLib.mkCargoDerivation {
  inherit cargoArtifacts pname src;

  buildPhaseCargoCommand = "cargo refinedrust -- --offline";
  nativeBuildInputs = [self.packages.${system}.default];

  cargoVendorDir = null;
  pnameSuffix = "-refinedrust";

  __contentAddressed = true;
  installPhase = ''
    RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
    cp -r $RR_OUTPUT_DIR $out
  '';
}
