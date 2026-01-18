{
  craneLib,
  hostPlatform,
  rrPkgs,
  pkgs,
}: {
  cargoExtraArgs ? "--locked",
  libDeps ? [],
  target ? hostPlatform,
  withStdlib ? true,
  ...
} @ origArgs: let
  args = builtins.removeAttrs origArgs [
    "libDeps"
    "target"
    "withStdlib"
  ];
in
  craneLib.mkCargoDerivation ({
      __contentAddressed = true;

      pnameSuffix = "-refinedrust";

      buildPhaseCargoCommand = ''
        cargo refinedrust -- ${cargoExtraArgs} \
        ${pkgs.lib.strings.optionalString (target == hostPlatform) (" " + ''--config target.${hostPlatform}.linker=\"${pkgs.gcc}/bin/cc\"'')}
      '';

      nativeBuildInputs =
        if withStdlib
        then [rrPkgs."target-${target}"]
        else [rrPkgs.frontend];

      RR_GENERATE_DUNE_PROJECT = true;
      RR_LIB_LOAD_PATHS =
        pkgs.lib.concatStringsSep ":" (libDeps ++ pkgs.lib.optionals withStdlib rrPkgs.stdlib.propagatedBuildInputs);

      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    }
    // args)
