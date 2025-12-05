{
  inputs,
  system,
}:
with inputs; rec {
  pkgs = import nixpkgs {inherit overlays system;};
  rrPkgs = self.packages.${system};

  overlays = let
    ocamlFlambda = import ./ocamlFlambdaOverlay.nix {inherit pkgs;};
  in [ocamlFlambda rust-overlay.overlays.default];

  mapToAttrs = fName: fValue: l: let
    f = {pname, ...} @ args: {
      name = fName pname;
      value = fValue args;
    };
  in
    pkgs.lib.listToAttrs (map f l);

  rocq = {
    mkDepRocqDerivation = import ./mkDepRocqDerivation.nix {inherit pkgs;};
  };

  rust =
    rec {
      hostPlatform = pkgs.stdenv.hostPlatform.rust.rustcTarget;
      mkToolchain = import ./mkRustToolchain.nix {inherit hostPlatform pkgs;};
    }
    // (import ./rustTools.nix {inherit crane pkgs rrPkgs;});
}
