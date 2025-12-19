{
  inputs,
  system,
}:
with inputs; rec {
  pkgs = import nixpkgs {inherit overlays system;};
  rrPkgs = self.packages.${system};

  overlays = [
    (import ./overlayOCamlFlambda.nix {})
    (import ./overlaySMTCoq.nix {})
    rust-overlay.overlays.default
  ];

  mapToAttrs = fName: fValue: l: let
    f = {pname, ...} @ args: {
      name = fName pname;
      value = fValue args;
    };
  in
    pkgs.lib.listToAttrs (map f l);

  rocq = {
    mkDepDerivation = import ./mkDepRocqDerivation.nix {inherit pkgs;};
    mkRefinedRust = import ./mkRocqRefinedRust.nix {
      inherit pkgs rrPkgs;
      inherit (rust) cargoRefinedRust;
    };
  };

  rust = let
    craneLib = crane.mkLib pkgs;
  in rec {
    inherit (craneLib) cargoDeny overrideToolchain;

    availableTargets = import ./availableTargets.nix {inherit pkgs rust-overlay;};

    cargoClippy = devToolchain: craneLib.cargoClippy.override {clippy = devToolchain;};
    cargoFmt = devToolchain: craneLib.cargoFmt.override {rustfmt = devToolchain;};
    cargoMachete = import ./cargoMachete.nix {inherit craneLib pkgs;};
    cargoRefinedRust = import ./cargoRefinedRust.nix {inherit craneLib rrPkgs pkgs;};
    cargoWorkspaceUnused = import ./cargoWorkspaceUnused.nix {inherit craneLib pkgs;};

    mkToolchain = channel: components:
      pkgs.rust-bin.fromRustupToolchain {
        inherit channel components;
        profile = "minimal";
      };
  };
}
