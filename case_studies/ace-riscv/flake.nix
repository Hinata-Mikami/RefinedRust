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
      target = "riscv64gc-unknown-none-elf";

      crossPkgs = import refinedrust.inputs.nixpkgs {
        inherit localSystem crossSystem;
      };
      pkgs = import refinedrust.inputs.nixpkgs {inherit localSystem;};

      toolchain =
        refinedrust.outputs.packages.${localSystem}."target-${target}".passthru.toolchain;

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

          installFlags = ["I=$(out)/opensbi-rust-bindings"];

          postInstall = ''
            ln -s $out/opensbi-rust-bindings/{lib64,lib}
          '';
        });

        securityMonitor = toolchain.envBuilder.buildPackage rec {
          inherit meta version;

          pname = "security-monitor";
          src = "${ACE-RISCV}/security-monitor";

          doCheck = false;

          cargoExtraArgs = "-Zbuild-std=core,alloc --target=${target} --config target.x86_64-unknown-linux-gnu.linker=\\\"/nix/store/kaj8d1zcn149m40s9h0xi0khakibiphz-gcc-wrapper-14.3.0/bin/cc\\\"";
          cargoVendorDir = toolchain.envBuilder.vendorMultipleCargoDeps {
            inherit (toolchain.envBuilder.findCargoFiles src) cargoConfigs;

            cargoLockList = [
              "${src}/Cargo.lock"
              "${toolchain.build.passthru.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
            ];
          };

          cargoArtifacts = toolchain.envBuilder.buildDepsOnly {
            inherit cargoExtraArgs cargoVendorDir doCheck meta pname src version;
          };

          INSTALL_DIR = packages.opensbi;
          LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];

          passthru = {inherit cargoArtifacts cargoExtraArgs cargoVendorDir pname src;};
        };

        securityMonitorRR = refinedrust.lib.${localSystem}.cargoRefinedRust {
          inherit (packages.securityMonitor.passthru) cargoArtifacts cargoExtraArgs cargoVendorDir pname src;
          inherit meta target version;

          INSTALL_DIR = packages.opensbi;
          LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];
        };

        ace = pkgs.rocqPackages.mkRocqDerivation rec {
          inherit meta version;

          pname = "ace";
          opam-name = "ace";

          src = "${ACE-RISCV}/verification";

          propagatedBuildInputs = [refinedrust.outputs.packages.${localSystem}.stdlib];
          useDune = true;
        };

        default = packages.securityMonitor;
      };

      formatter = pkgs.alejandra;
    });
}
