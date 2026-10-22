{
  equations,
  stdpp,
  iris,
  iris-contrib,
  lambda-rust,
  smtcoq,
  sniper,
  verit,
}:
let
  mkRocqPackages =
    base:
    base.overrideScope (
      final: prev: {
        mkRocqDerivation =
          let
            preBuild = ''
              dune() { command dune $@ --display=short; }
            '';
          in
          args: prev.mkRocqDerivation ({ inherit preBuild; } // args);

        stdpp = final.lib.overrideRocqDerivation {
          defaultVersion = stdpp.version;
          release.${stdpp.version}.sha256 = stdpp.sha256;
          releaseRev = v: v;
        } prev.stdpp;

        iris = final.lib.overrideRocqDerivation {
          defaultVersion = iris.version;
          release.${iris.version}.sha256 = iris.sha256;
          releaseRev = v: v;
        } prev.iris;

        # NOTE: Remove `equations` when available in Nix's `RocqPackages`
        equations = final.callPackage ./equations.nix equations;

        # NOTE: Remove `extlib` when available in Nix's `RocqPackages`
        extlib = final.callPackage ./extlib.nix { };

        # NOTE: Remove `iris-contrib` when available in Nix's `RocqPackages`
        iris-contrib = final.callPackage ./iris-contrib.nix iris-contrib;

        # NOTE: Remove `lambda-rust` when available in Nix's `RocqPackages`
        lambda-rust = final.callPackage ./lambda-rust.nix lambda-rust;

        smtcoq = final.lib.overrideRocqDerivation {
          defaultVersion = smtcoq.version;
          release.${smtcoq.version}.sha256 = smtcoq.sha256;
        } prev.smtcoq;

        sniper = final.lib.overrideRocqDerivation {
          defaultVersion = sniper.version;
          release.${sniper.version}.sha256 = sniper.sha256;
        } prev.sniper;
      }
    );
in
final: prev: {
  rocqPackages = mkRocqPackages prev.rocqPackages_9_2;

  verit = prev.verit.overrideAttrs (old: {
    inherit (verit) version src;
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ final.pkg-config ];
    patchPhase = "";
  });
}
