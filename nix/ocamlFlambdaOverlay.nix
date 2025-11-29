{pkgs}: _: prev: rec {
  # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
  # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.05/pkgs/applications/science/logic/rocq-core/default.nix#L15
  ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (_: prev: {
    ocaml = prev.ocaml.override {flambdaSupport = true;};

    # NOTE: Remove this when `dune` will handle `rocq` subcommands
    # See: https://github.com/ocaml/dune/issues/11572
    dune_3 = prev.dune_3.overrideAttrs (prev: {
      nativeBuildInputs = prev.nativeBuildInputs ++ [pkgs.makeWrapper];

      postFixup = let
        coqSubcommand = newCmd: oldCmd:
          pkgs.writeScriptBin oldCmd ''
            #!/bin/sh
            unset COQPATH
            rocq ${newCmd} "$@"
          '';

        coqc = coqSubcommand "compile" "coqc";
        coqdep = coqSubcommand "dep" "coqdep";
        coqpp = coqSubcommand "pp-mlg" "coqpp";
      in ''
        wrapProgram $out/bin/dune \
          --prefix PATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
          --prefix OCAMLPATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
          --run "export COQPATH=\$(eval echo \$ROCQPATH)"
      '';
    });
  });

  rocqPackages = prev.rocqPackages.overrideScope (_: prev: {
    mkRocqDerivation = args:
      prev.mkRocqDerivation ({
          preBuild = ''
            dune() { command dune $@ --display=short; }
          '';
        }
        // args);

    rocq-core =
      prev.rocq-core.override {customOCamlPackages = ocamlPackages;};
  });
}
