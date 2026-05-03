pkgs: prev: rec {
  verit = prev.verit.overrideAttrs (old: {
    src = pkgs.fetchFromGitLab {
      domain = "gitlab.mpi-sws.org";
      owner = "lgaeher";
      repo = "verit";
      rev = "6348b82f16c7cd2eb2a0b8f2b48d3f35cbb62b90";
      sha256 = "sha256-DMSVU39uNr8Bnx6TevODF27MecMCsoaTdoHu5mi1oZ0=";
    };
    version = "6348b82f";
    nativeBuildInputs = old.nativeBuildInputs ++ [pkgs.pkg-config];
  });

  rocqPackages = prev.rocqPackages.overrideScope (final: prev: {
    # NOTE: Remove `metarocq-template` when available in Nix's `RocqPackages`
    metarocq-template = let
      version = "v1.4.1-9.1";
      release.${version}.sha256 = "sha256-tzoAWX74lg7pArGVP11QBvDRKMvmGxXvrf3+1E3Y4DI=";

      repo = "metarocq";
      owner = "MetaRocq";

      mlPlugin = true;

      utils = final.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-utils";
        preBuild = "cd utils";
        propagatedBuildInputs = [final.equations];
      };

      common = final.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-common";
        preBuild = "cd common";
        propagatedBuildInputs = [final.equations utils];

        patchPhase = "patchShebangs ./configure.sh";
        configurePhase = "./configure.sh";
      };
    in
      final.mkRocqDerivation rec {
        inherit mlPlugin owner release repo version;

        pname = "metarocq-template-rocq";
        preBuild = "cd template-rocq";
        propagatedBuildInputs = [final.equations common utils];

        patchPhase = ''
          patchShebangs ./configure.sh
          patchShebangs ./template-rocq/update_plugin.sh
          patchShebangs ./template-rocq/gen-src/to-lower.sh
          sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-rocq/gen-src/to-lower.sh
          sed -i -e 's/coq-core/rocq-runtime/g' template-rocq/META.rocq-metarocq-template-rocq
        '';
        configurePhase = "./configure.sh";
      };

    # NOTE: Remove `rocq-elpi` when upgrading to Nix 26.05
    rocq-elpi = prev.rocq-elpi.overrideAttrs {
      src = pkgs.fetchFromGitHub {
        owner = "LPCIC";
        repo = "coq-elpi";
        rev = "6bfdad614d819c8dcec6c83cc21ba4166b535e7c";
        hash = "sha256-/ehf2g/+riXOmfXs90Mx0PnKA0wJyombHK+rbVePjw0=";
      };

      propagatedBuildInputs = with prev.rocq-core.ocamlPackages; [
        findlib
        ppx_optcomp
        (elpi.override {version = "3.6.1";})
      ];
    };

    trakt = final.mkRocqDerivation rec {
      version = "aa76ebdf4cc6323cf08c65e56f8ba8580d79f7a2";

      pname = "trakt";
      owner = "rocq-trakt";
      repo = "trakt";

      propagatedBuildInputs = [final.rocq-elpi final.stdlib];

      preBuild = ''
        sed -i -e 's/coq_makefile/rocq makefile/g' Makefile
      '';

      release.${version}.sha256 = "sha256-3kqRfl7dvmXa9UvBI+UJ5iXl578ZHT1+wpMQX94ByKQ=";
    };
  });
}
