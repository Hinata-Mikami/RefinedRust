{pkgs}: pin: {
  pname,
  propagatedBuildInputs ? [pkgs.rocqPackages.stdlib],
  owner ? "iris",
}:
pkgs.rocqPackages.mkRocqDerivation {
  inherit pname propagatedBuildInputs owner;

  domain = "gitlab.mpi-sws.org";
  # NOTE: Remove `sed` line when Makefiles will be updated upstream
  preBuild = ''
    sed -i -e 's/"$(COQBIN)coq_makefile"/"$(COQBIN)rocq" makefile/g' Makefile
    patchShebangs coq-lint.sh
  '';

  release.${pin.version}.sha256 = "${pin.sha256}";
  version = pin.version;
}
