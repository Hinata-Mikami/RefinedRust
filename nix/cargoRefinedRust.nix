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
      __contentAddressed = true;

      pnameSuffix = "-refinedrust";

      buildPhaseCargoCommand = "cargo refinedrust -- ${cargoExtraArgs}";
      nativeBuildInputs = [self.packages.${system}."target-${target}"];

      RR_GENERATE_DUNE_PROJECT = 1; 

      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    })
