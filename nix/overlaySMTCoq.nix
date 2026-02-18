_: pkgs: prev: rec {
  verit = prev.verit.overrideAttrs {
    src = pkgs.fetchurl {
      url = "https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz";
      sha256 = "sha256-ibQa2nFR2sKQ+LyxWK6dH8etB6NiZGFXy0yCws7w9OU=";
    };
    version = "9f48a98";

    patchPhase = ''
      # Compilation patches
      sed -i -e '3i#include "DAG-print.h"' src/instantiation/ccfv-{constr,mod}.c
      sed -i -e '4iconst char *byte_to_binary(unsigned x, unsigned size);' src/instantiation/ccfv-mod.c
      sed -i -e '248iTproof proof_tmp_eq_norm(Tproof clause, TDAG DAG);' src/proof/proof.h

      # Multiple definition patches
      sed -i -e 's/bb_data/bb_data_xx/g' src/arith/LA-xx.c.tpl
      sed -i -e 's/conflict_eqs/conflict_eqs_xx/g' src/arith/LA-xx.c.tpl
      sed -i -e 's/conflict_lits/conflict_lits_xx/g' src/arith/LA-xx.c.tpl
      sed -i -e 's/LA_bound_ranking/LA_bound_ranking_xx/g' src/arith/LA-xx.c.tpl
      sed -i -e 's/veriT_conflict_eqs_xx/veriT_conflict_eqs/g' src/arith/LA-xx.c.tpl
      sed -i -e '200iextern' src/arith/simplex-xx.c.tpl
      sed -i -e '3iTstack_simplex_var integer_stack;' src/arith/simplex.c
      sed -i -e '2350d' src/congruence/congruence.c
      sed -i -e '28,32d' src/instantiation/inst-man.c
      sed -i -e '20iextern' src/instantiation/inst-trigger.c
      sed -i -e '403iextern' src/SAT/veriT-SAT.h
      sed -i -e '29d' src/parsers/tptp/tptplex.l
    '';
  };

  zchaff = prev.zchaff.overrideAttrs {
    version = "2008.10.12";
    src = pkgs.fetchzip {
      url = "http://www.princeton.edu/~chaff/zchaff/zchaff.2008.10.12.zip";
      sha256 = "sha256-sFH+6vhQPkCgmzeMmz1BBykVxZi5uoV0g/gIVGlLS+s=";
    };
  };

  # NOTE: Remove `metarocq-template-rocq` when available in Nix's `RocqPackages`
  rocqPackages = prev.rocqPackages.overrideScope (_: prev: {
    metarocq-template = let
      version = "v1.4.1-9.1";
      release.${version}.sha256 = "sha256-tzoAWX74lg7pArGVP11QBvDRKMvmGxXvrf3+1E3Y4DI=";

      repo = "metarocq";
      owner = "MetaRocq";

      mlPlugin = true;

      utils = pkgs.rocqPackages.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-utils";
        preBuild = "cd utils";
        propagatedBuildInputs = [pkgs.rocqPackages.equations];
      };

      common = pkgs.rocqPackages.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-common";
        preBuild = "cd common";
        propagatedBuildInputs = [pkgs.rocqPackages.equations utils];

        patchPhase = "patchShebangs ./configure.sh";
        configurePhase = "./configure.sh";
      };
    in
      pkgs.rocqPackages.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-template-rocq";
        preBuild = "cd template-rocq";
        propagatedBuildInputs = [pkgs.rocqPackages.equations common utils];

        patchPhase = ''
          patchShebangs ./configure.sh
          patchShebangs ./template-rocq/update_plugin.sh
          patchShebangs ./template-rocq/gen-src/to-lower.sh
          sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-rocq/gen-src/to-lower.sh
          sed -i -e 's/coq-core/rocq-runtime/g' template-rocq/META.rocq-metarocq-template-rocq
        '';
        configurePhase = "./configure.sh";
      };

    trakt = pkgs.rocqPackages.mkRocqDerivation rec {
      version = "aa76ebdf4cc6323cf08c65e56f8ba8580d79f7a2";

      pname = "trakt";
      owner = "rocq-trakt";
      repo = "trakt";

      propagatedBuildInputs = [pkgs.rocqPackages.rocq-elpi pkgs.rocqPackages.stdlib];

      preBuild = ''
        sed -i -e 's/coq_makefile/rocq makefile/g' Makefile
      '';

      release.${version}.sha256 = "sha256-3kqRfl7dvmXa9UvBI+UJ5iXl578ZHT1+wpMQX94ByKQ=";
    };
  });
}
