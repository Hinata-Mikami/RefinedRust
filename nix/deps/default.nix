{
  equations,
  stdpp,
  iris,
  iris-contrib,
  lambda-rust,
  smtcoq,
  sniper,
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

        # NOTE: Remove `iris-contrib` when available in Nix's `RocqPackages`
        iris-contrib = final.callPackage ./iris-contrib.nix iris-contrib;

        # NOTE: Remove `lambda-rust` when available in Nix's `RocqPackages`
        lambda-rust = final.callPackage ./lambda-rust.nix lambda-rust;

        smtcoq = final.lib.overrideRocqDerivation {
          defaultVersion = smtcoq.version;
          release.${smtcoq.version}.sha256 = smtcoq.sha256;
        } prev.smtcoq;

        # NOTE: Remove `metarocq-template-rocq` when available in `smtcoq/sniper` repository
        metarocq-template = final.callPackage ./metarocq-template.nix { };

        # NOTE: Remove `sniper` when available in `smtcoq/sniper` repository
        sniper = final.callPackage ./sniper.nix sniper;
      }
    );
in
_: prev: {
  rocqPackages = mkRocqPackages prev.rocqPackages;
}
