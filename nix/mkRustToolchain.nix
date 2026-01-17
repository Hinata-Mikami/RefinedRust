{
  hostPlatform,
  pkgs,
}: channel: components: target:
pkgs.rust-bin.fromRustupToolchain {
  inherit channel;

  components = components ++ (pkgs.lib.lists.optional (target != hostPlatform) "rust-src");

  profile = "minimal";
  targets = [target];
}
