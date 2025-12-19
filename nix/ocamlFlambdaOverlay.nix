{pkgs}: _: prev: rec {
  # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
  # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.11/pkgs/applications/science/logic/rocq-core/default.nix#L16
  ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (_: prev: {
    ocaml = prev.ocaml.override {flambdaSupport = true;};

    dune_3 = prev.dune_3.overrideAttrs rec {
      version = "3.21.0~alpha4";

      src = pkgs.fetchurl {
        url = "https://github.com/ocaml/dune/releases/download/3.21.0_alpha4/dune-3.21.0.alpha4.tbz";
        hash = "sha256-PSuZtghLx0+qSoyFnqHwPhz1jfi3EbgL/rhdxRGva08=";
      };
    };
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

    # NOTE: Remove `equations` when available in Nix's `RocqPackages`
    equations = pkgs.rocqPackages.mkRocqDerivation {
      pname = "equations";
      owner = "mattam82";
      repo = "Coq-Equations";
      opam-name = "rocq-equations";

      propagatedBuildInputs = [pkgs.rocqPackages.stdlib pkgs.ocamlPackages.ppx_optcomp];

      mlPlugin = true;
      useDune = true;

      version = "2ce6d98dd03979369d739ac139db4da4f7eab352";
      release = {
        "2ce6d98dd03979369d739ac139db4da4f7eab352".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
      };
    };
  });
}
