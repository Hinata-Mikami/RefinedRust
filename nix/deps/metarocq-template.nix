{
  # Libraries
  mkRocqDerivation,
  # Dependencies
  equations,
  extlib,
  # Arguments
  sha256 ? null,
  version ? "main",
}:
let
  version = "v1.5.1-9.2";
  release.${version}.sha256 = "sha256-sinpbes0dEg2dGueu90ckY+qoyzeUS0uG6RrozHN86E=";

  repo = "metarocq";
  owner = "MetaRocq";

  mlPlugin = true;

  utils = mkRocqDerivation rec {
    inherit
      mlPlugin
      owner
      release
      repo
      version
      ;

    pname = "metarocq-utils";
    preBuild = "cd utils";
    propagatedBuildInputs = [
      equations
      extlib
    ];
  };

  common = mkRocqDerivation rec {
    inherit
      mlPlugin
      owner
      release
      repo
      version
      ;

    pname = "metarocq-common";
    preBuild = "cd common";
    propagatedBuildInputs = [
      equations
      extlib
      utils
    ];

    patchPhase = "patchShebangs ./configure.sh";
    configurePhase = "./configure.sh";
  };
in
mkRocqDerivation rec {
  inherit
    mlPlugin
    owner
    release
    repo
    version
    ;

  pname = "metarocq-template-rocq";
  preBuild = "cd template-rocq";
  propagatedBuildInputs = [
    equations
    common
    utils
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./template-rocq/update_plugin.sh
    patchShebangs ./template-rocq/gen-src/to-lower.sh
    sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-rocq/gen-src/to-lower.sh
    sed -i -e 's/coq-core/rocq-runtime/g' template-rocq/META.rocq-metarocq-template-rocq
  '';
  configurePhase = "./configure.sh";
}
