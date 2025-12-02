{
  craneLib,
  self,
  system,
  pkgs,
}: let
  hostPlatform = pkgs.stdenv.hostPlatform.rust.rustcTarget;
in
  {
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
        __contentAddressed = false; # TODO: Make RefinedRust frontend's output deterministic

        pnameSuffix = "-refinedrust";

        buildPhaseCargoCommand =
          "cargo refinedrust -- ${cargoExtraArgs}"
          + (
            if target == hostPlatform
            then ""
            else " --config target.${hostPlatform}.linker=\\\"${pkgs.gcc}/bin/cc\\\""
          );

        nativeBuildInputs =
          if withStdlib
          then [self.packages.${system}."target-${target}"]
          else [self.packages.${system}.frontend];

        RR_GENERATE_DUNE_PROJECT = true;
        RR_LIB_LOAD_PATHS =
          pkgs.lib.concatStringsSep ":" (libDeps ++ pkgs.lib.optionals withStdlib self.packages.${system}.stdlib.propagatedBuildInputs);

        installPhase = ''
          RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
          cp -r $RR_OUTPUT_DIR $out
        '';
      }
      // args)
