{
  # Libraries
  mkRocqDerivation,
  # Dependencies
  iris,
  # Arguments
  sha256 ? null,
  version ? "main",
}:
mkRocqDerivation {
  inherit version;

  domain = "gitlab.mpi-sws.org";
  owner = "iris";
  pname = "lambda-rust";

  propagatedBuildInputs = [ iris ];

  release.${version}.sha256 = sha256;
}
