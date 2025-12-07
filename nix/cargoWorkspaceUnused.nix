{
  craneLib,
  pkgs,
}: devToolchain: {
  pname,
  src,
}: let
  cargo-workspace-unused = (craneLib.overrideToolchain devToolchain).buildPackage {
    src = pkgs.fetchCrate {
      pname = "cargo-workspace-unused-pub";
      version = "0.1.0";
      sha256 = "sha256-T0neI46w2u4hD1QvpF/qsCt8oH2bdyck8s9iNKMikCE=";
    };
  };
in
  craneLib.mkCargoDerivation {
    inherit pname src;

    buildPhaseCargoCommand = ''
      rust-analyzer scip . --output index.scip
      cargo workspace-unused-pub --extensions rs,unused
    '';
    nativeBuildInputs = [cargo-workspace-unused devToolchain];

    cargoArtifacts = null;
    doInstallCargoArtifacts = false;
    pnameSuffix = "-workspace-unused";
  }
