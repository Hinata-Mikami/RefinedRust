{
  # Libraries
  mkRocqDerivation,
  # Dependencies
  metarocq-template,
  smtcoq,
  rocq-core,
  # Arguments
  sha256 ? null,
  version ? "main",
}:
mkRocqDerivation {
  inherit version;

  owner = "lafeychine";
  pname = "sniper";

  mlPlugin = true;
  propagatedBuildInputs = [
    rocq-core.ocamlPackages.num
    metarocq-template
    smtcoq
  ];

  release.${version}.sha256 = sha256;
}
