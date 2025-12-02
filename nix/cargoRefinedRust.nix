{
  craneLib,
  self,
  system,
  pkgs,
}: {
  cargoExtraArgs ? "--locked",
  libDeps ? [],
  target ? pkgs.stdenv.hostPlatform.rust.rustcTarget,
  withStdlib ? true,
  ...
} @ origArgs: let
  args = builtins.removeAttrs origArgs [
    "target"
    "withStdlib"
  ];
in
  craneLib.mkCargoDerivation ({
      __contentAddressed = false; # TODO: Make RefinedRust frontend's output deterministic

      pnameSuffix = "-refinedrust";

      buildPhaseCargoCommand = "cargo refinedrust -- ${cargoExtraArgs}";
      nativeBuildInputs =
        if withStdlib
        then [self.packages.${system}."target-${target}"]
        else [self.packages.${system}.frontend];

      RR_LIB_LOAD_PATHS =
        pkgs.lib.concatStringsSep ":" (libDeps ++ pkgs.lib.optionals withStdlib self.packages.${system}.stdlib.propagatedBuildInputs);

      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    }
    // args)
