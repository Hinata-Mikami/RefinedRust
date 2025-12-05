{
  hostPlatform,
  pkgs,
}: let
  addComponent = component: {extensions = [component];};
  addTarget = target: {targets = [target];};
in
  channel: components: target: let
    toolchain = {
      inherit channel components;
      profile = "minimal";
    };
  in
    (pkgs.rust-bin.fromRustupToolchain toolchain // addTarget target).override (
      pkgs.lib.attrsets.optionalAttrs (target != hostPlatform) (addComponent "rust-src")
    )
