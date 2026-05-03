{
  craneLib,
  frontend,
  stdlib,
  pkgs,
}: {
  cargoExtraArgs ? "--locked",
  libDeps ? [],
  toolchain,
  withStdlib ? true,
  ...
} @ origArgs: let
  args = builtins.removeAttrs origArgs [
    "libDeps"
    "toolchain"
    "withStdlib"
  ];
in
  (craneLib.overrideToolchain toolchain).mkCargoDerivation ({
      __contentAddressed = true;

      pnameSuffix = "-refinedrust";

      buildPhaseCargoCommand = "cargo refinedrust -- ${cargoExtraArgs}";

      nativeBuildInputs = [toolchain frontend] ++ pkgs.lib.optionals withStdlib [stdlib];

      env.LD_LIBRARY_PATH = "${toolchain}/lib:${toolchain}/lib/rustlib/x86_64-unknown-linux-gnu/lib";

      RR_GENERATE_DUNE_PROJECT = true;
      RR_LIB_LOAD_PATHS =
        pkgs.lib.concatStringsSep ":" (libDeps ++ pkgs.lib.optionals withStdlib stdlib.propagatedBuildInputs);
      RR_NIX_STDLIB = pkgs.lib.optionalString withStdlib "${stdlib}/share";

      installPhase = ''
        RR_OUTPUT_DIR=$(cargo refinedrust --show-config | grep output_dir | cut -d' ' -f3 | tr '"' ' ')
        cp -r $RR_OUTPUT_DIR $out
      '';
    }
    // args)
