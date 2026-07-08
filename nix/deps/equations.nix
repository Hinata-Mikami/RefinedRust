{
  # Libraries
  mkRocqDerivation,
  # Dependencies
  stdlib,
  rocq-core,
  # Arguments
  sha256 ? null,
  version ? "main",
}:
mkRocqDerivation {
  inherit version;

  pname = "equations";
  owner = "mattam82";
  repo = "Coq-Equations";
  opam-name = "rocq-equations";

  propagatedBuildInputs = [stdlib rocq-core.ocamlPackages.ppx_optcomp];

  mlPlugin = true;
  useDune = true;

  release.${version}.sha256 = sha256;

  patchPhase = ''
    sed -i -e 's/(lang dune 3.13)/(lang dune 3.21)/g' dune-project
    sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
    sed -i -e 's/coq-core/rocq-runtime/g' src/dune
    sed -i -e 's/coq/rocq/g' examples/dune src/dune theories/dune theories/Prop/dune theories/Type/dune test-suite/dune
  '';
}
