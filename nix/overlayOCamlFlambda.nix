final: prev: rec {
  # NOTE: Remove `ocamlPackages` when upgrading to Nix 26.05
  # NOTE: Then, rename this file `overlayRocqCompat.nix`
  ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (_: prev: {
    ocaml = prev.ocaml.override {flambdaSupport = true;};

    dune_3 = prev.dune_3.overrideAttrs rec {
      version = "3.21.0";

      src = final.fetchurl {
        url = "https://github.com/ocaml/dune/releases/download/3.21.0/dune-3.21.0.tbz";
        hash = "sha256-521NiTaKCnACUZOur098W1QDHbo/Wb+dKvGXHcDs7d0=";
      };
    };
  });

  rocqPackages = prev.rocqPackages.overrideScope (final: prev: rec {
    dune = ocamlPackages.dune_3;

    mkRocqDerivation = args:
      prev.mkRocqDerivation ({
          preBuild = ''
            dune() { command dune $@ --display=short; }
          '';
        }
        // args);

    rocq-core = prev.rocq-core.override {
      inherit dune;

      customOCamlPackages = ocamlPackages;
      version = "9.1";
    };

    # NOTE: Remove `equations` when available in Nix's `RocqPackages`
    equations = final.mkRocqDerivation {
      pname = "equations";
      owner = "mattam82";
      repo = "Coq-Equations";
      opam-name = "rocq-equations";

      propagatedBuildInputs = with final; [stdlib rocq-core.ocamlPackages.ppx_optcomp];

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
