{
  craneLib,
  self,
  system,
  pkgs,
}: {
  cargoExtraArgs ? "--locked",
  target ? pkgs.stdenv.hostPlatform.rust.rustcTarget,
  withStdlib ? true,
  ...
} @ origArgs: let
  args = builtins.removeAttrs origArgs [
    "target"
    "withStdlib"
  ];
in
  craneLib.mkCargoDerivation (args
    // {
      __contentAddressed = true;

      pnameSuffix = "-refinedrust";

      buildPhaseCargoCommand = "cargo refinedrust -- ${cargoExtraArgs}";
      nativeBuildInputs =
        if withStdlib
        then [self.packages.${system}."target-${target}"]
        else [self.packages.${system}.frontend];

      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    })
