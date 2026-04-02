{
  cargoRefinedRust,
  pkgs,
  rrPkgs,
}: {
  libDeps ? [],
  opam-name ? pname,
  pname,
  propagatedBuildInputs ? [],
  src,
  generateFiles ? true,
  useDune ? true,
  withStdlib ? true,
  withTheories ? false,
  cargoRefinedRustArgs ? {},
  rocqArgs ? {},
  rocqTheoriesArgs ? {},
  ...
} @ origArgs: let
  args = let
    fullArgs = origArgs // {inherit cargoRefinedRustArgs libDeps opam-name propagatedBuildInputs rocqArgs rocqTheoriesArgs src useDune generateFiles withTheories;};
    commonRemoveAttrs = ["cargoRefinedRustArgs" "pname" "propagatedBuildInputs" "rocqArgs" "rocqTheoriesArgs" "withTheories"];
  in rec {
    cargo = builtins.removeAttrs fullArgs (commonRemoveAttrs ++ ["opam-name" "useDune" "generateFiles"]);
    rocq = builtins.removeAttrs fullArgs (commonRemoveAttrs ++ ["cargoArtifacts" "cargoExtraArgs" "cargoVendorDir" "libDeps" "src" "toolchain" "generateFiles" "withStdlib"]);
    rocqTheories = builtins.removeAttrs rocq ["opam-name"];
  };

  theories = pkgs.rocqPackages.mkRocqDerivation ({
      src = "${src}/theories";
      propagatedBuildInputs =
        (pkgs.lib.optionals withStdlib [rrPkgs.stdlib rrPkgs.solver])
        ++ libDeps
        ++ propagatedBuildInputs;

      pname = "refinedrust-" + pname + "-theories";
      opam-name = opam-name + "-theories";
    }
    // args.rocqTheories // rocqTheoriesArgs);
in
  pkgs.rocqPackages.mkRocqDerivation ({
      src =
        if generateFiles
        then cargoRefinedRust (args.cargo // cargoRefinedRustArgs)
        else src;
      pname = "refinedrust-" + pname;

      propagatedBuildInputs =
        (pkgs.lib.optionals withStdlib [rrPkgs.stdlib rrPkgs.solver])
        ++ libDeps
        ++ propagatedBuildInputs
        ++ (pkgs.lib.optionals withTheories [theories]);

      postInstall = let
        name = pkgs.lib.replaceStrings ["-" "_"] ["/" "/"] pname;
      in ''
        mkdir -p $out/share/${name}
        find . -name "interface.rrlib" -exec cp {} $out/share/${name}/. \;
      '';
    }
    // args.rocq // rocqArgs)
