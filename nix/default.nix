{
  crane,
  nixpkgs,
  rust-overlay,
}:

with nixpkgs.lib;
rec {
  mapToAttrs =
    fValue: l:
    let
      f = { pname, ... }@args: nameValuePair pname (fValue args);
    in
    listToAttrs (map f l);

  mkDevContainer = import ./mkDevContainer.nix;

  mkDuneWrapper = import ./mkDuneWrapper.nix;

  rocq = {
    mkRefinedRust =
      pkgs: frontend: stdlib:
      import ./mkRocqRefinedRust.nix {
        inherit pkgs stdlib;
        cargoRefinedRust = rust.cargoRefinedRust pkgs frontend stdlib;
      };
  };

  rust = {
    # Libraries
    availableTargets = pkgs: import ./availableTargets.nix { inherit pkgs rust-overlay; };
    mkToolchain =
      pkgs: channel: components:
      pkgs.rust-bin.fromRustupToolchain {
        inherit channel components;
        profile = "minimal";
      };
    overrideToolchain = pkgs: (crane.mkLib pkgs).overrideToolchain;

    # Tools
    cargoClippy =
      pkgs: devToolchain: (crane.mkLib pkgs).cargoClippy.override { clippy = devToolchain; };
    cargoDeny = pkgs: (crane.mkLib pkgs).cargoDeny;
    cargoFmt = pkgs: devToolchain: (crane.mkLib pkgs).cargoFmt.override { rustfmt = devToolchain; };

    cargoMachete =
      pkgs:
      import ./cargoMachete.nix {
        inherit pkgs;
        craneLib = crane.mkLib pkgs;
      };

    cargoRefinedRust =
      pkgs: frontend: stdlib:
      import ./cargoRefinedRust.nix {
        inherit frontend pkgs stdlib;
        craneLib = crane.mkLib pkgs;
      };

    cargoWorkspaceUnused =
      pkgs:
      import ./cargoWorkspaceUnused.nix {
        inherit pkgs;
        craneLib = crane.mkLib pkgs;
      };
  };
}
