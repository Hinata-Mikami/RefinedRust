{
  craneLib,
  self,
  system,
  pkgs,
}: {
  cargoExtraArgs ? "",
  target ? pkgs.stdenv.hostPlatform.rust.rustcTarget,
  ...
} @ origArgs: let
  args = builtins.removeAttrs origArgs [
    "target"
  ];
in
  craneLib.mkCargoDerivation (args
    // {
      buildPhaseCargoCommand = "cargo refinedrust -- ${cargoExtraArgs}";
      nativeBuildInputs = [self.packages.${system}."target-${target}"];

      pnameSuffix = "-refinedrust";

      __contentAddressed = true;
      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    })
