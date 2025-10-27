{
  inputs = {
    refinedrust.url = "git+file://../../..";

    ACE-RISCV = {
      url = "github:IBM/ACE-RISCV";
      flake = false;
    };
  };

  outputs = {
    self,
    ACE-RISCV,
    refinedrust,
  }:
    refinedrust.inputs.flake-utils.lib.eachDefaultSystem (localSystem: let
      crossSystem = "riscv64-linux";
      crossSystemRust = "riscv64gc-unknown-none-elf";

      crossPkgs = import refinedrust.inputs.nixpkgs {inherit localSystem crossSystem;};
      pkgs = import refinedrust.inputs.nixpkgs {inherit localSystem;};

      toolchain = refinedrust.outputs.packages.${localSystem}.target.${crossSystemRust}.passthru.toolchain;

      version = "0.4.0";
      meta = with pkgs.lib; {
        homepage = "https://github.com/IBM/ACE-RISCV";
        license = licenses.asl20;
      };
    in rec {
      packages = {
        opensbi = crossPkgs.opensbi.overrideAttrs (prev: rec {
          version = "92e8affb31b21ddc5d1193cf754ce644db7b460a";

          src = pkgs.fetchFromGitHub {
            owner = "riscv-software-src";
            repo = "opensbi";
            rev = version;
            hash = "sha256-82DE+lLeaUdscl5sH/KZDr91s8rEsy+/WVsrr3vI+SM=";
          };

          makeFlags = [
            "PLATFORM=generic"
            "PLATFORM_RISCV_ABI=lp64d"
            "PLATFORM_RISCV_ISA=rv64gc"
            "PLATFORM_RISCV_XLEN=64"
            "CROSS_COMPILE=riscv64-unknown-linux-gnu-"
          ];

          installFlags = [
            "I=$(out)/opensbi-rust-bindings"
          ];

          postInstall = ''
            ln -s $out/opensbi-rust-bindings/{lib64,lib}
          '';
        });

        security-monitor = let
          src = "${ACE-RISCV}/security-monitor";
          pname = "security-monitor";
        in
          toolchain.envBuilder.buildPackage rec {
            inherit meta pname src version;

            cargoExtraArgs = "-Zbuild-std=core,alloc --target=${crossSystemRust}";
            cargoVendorDir = toolchain.envBuilder.vendorMultipleCargoDeps {
              inherit (toolchain.envBuilder.findCargoFiles src) cargoConfigs;
              cargoLockList = [
                "${src}/Cargo.lock"
                "${toolchain.build.passthru.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
              ];
            };

            INSTALL_DIR = packages.opensbi;
            LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];

            doCheck = false;
          };

        default = packages.security-monitor;
      };

      formatter = pkgs.alejandra;
    });
}
