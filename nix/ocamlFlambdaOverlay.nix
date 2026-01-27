{pkgs}: _: prev: rec {
  # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
  # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.11/pkgs/applications/science/logic/rocq-core/default.nix#L16
  ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (_: prev: {
    ocaml = prev.ocaml.override {flambdaSupport = true;};

    dune_3 = prev.dune_3.overrideAttrs rec {
      version = "3.21.0";

      src = pkgs.fetchurl {
        url = "https://github.com/ocaml/dune/releases/download/3.21.0/dune-3.21.0.tbz";
        hash = "sha256-521NiTaKCnACUZOur098W1QDHbo/Wb+dKvGXHcDs7d0=";
      };
    };
  });

  rocqPackages = prev.rocqPackages.overrideScope (_: prev: rec {
    dune = ocamlPackages.dune_3;

    mkRocqDerivation = args:
      prev.mkRocqDerivation ({
          preBuild = ''
            dune() { command dune $@ --display=short; }
          '';
        }
        // args);

    rocq-core = pkgs.rocq-core_9_1.override {
      inherit dune;
      customOCamlPackages = ocamlPackages;
    };

    # NOTE: Remove `equations` when available in Nix's `RocqPackages`
    equations = pkgs.rocqPackages.mkRocqDerivation {
      pname = "equations";
      owner = "mattam82";
      repo = "Coq-Equations";
      opam-name = "rocq-equations";

      propagatedBuildInputs = [pkgs.rocqPackages.stdlib pkgs.ocamlPackages.ppx_optcomp];

      mlPlugin = true;
      useDune = true;

      version = "v1.3.1-9.1";
      release = {
        "v1.3.1-9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";
      };

      patchPhase = ''
        sed -i -e 's/(lang dune 3.13)/(lang dune 3.21)/g' dune-project
        sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
        sed -i -e 's/coq-core/rocq-runtime/g' src/dune
        sed -i -e 's/coq/rocq/g' examples/dune src/dune theories/dune theories/Prop/dune theories/Type/dune test-suite/dune
      '';
    };
  });
}
