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
      lib = refinedrust.lib.${localSystem};
      rrPackages = refinedrust.outputs.packages.${localSystem};
      pkgs = lib.pkgs;

      crossSystem = "riscv64-linux";
      target = "riscv64gc-unknown-none-elf";

      crossPkgs = import refinedrust.inputs.nixpkgs {
        inherit localSystem crossSystem;
      };

      toolchain = rrPackages."target-${target}".passthru.toolchain;

      ace = rec {
        version = "0.4.0";
        src = "${ACE-RISCV}/security-monitor";

        meta = with pkgs.lib; {
          homepage = "https://github.com/IBM/ACE-RISCV";
          license = licenses.asl20;
        };

        doCheck = false;
        cargoExtraArgs = "-Zbuild-std=core,alloc --target=${target}";
        cargoVendorDir = toolchain.envBuilder.vendorMultipleCargoDeps {
          inherit (toolchain.envBuilder.findCargoFiles src) cargoConfigs;

          cargoLockList = [
            "${src}/Cargo.lock"
            "${toolchain.build.passthru.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
          ];
        };
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

        pointersUtility = pkgs.rocqPackages.mkRocqDerivation rec {
          inherit (ace) meta version;

          pname = "pointers-utility";
          opam-name = "pointers-utility";

          src = lib.cargoRefinedRust rec {
            inherit (ace) cargoVendorDir doCheck meta src version;
            inherit pname target;

            cargoExtraArgs = ace.cargoExtraArgs + " --package pointers_utility";

            cargoArtifacts = toolchain.envBuilder.buildDepsOnly {
              inherit (ace) cargoVendorDir doCheck meta src version;
              inherit cargoExtraArgs pname;
            };

            preBuild = ''
              sed -i -e '11i#![rr::package("pointers-utility")]' ./rust-crates/pointers_utility/src/lib.rs
              cp --no-preserve=mode -r ${ACE-RISCV}/verification/{RefinedRust.toml,extra_specs.v,rust_proofs} .
            '';
          };

          propagatedBuildInputs = [rrPackages.stdlib];
          useDune = true;

          postInstall = ''
            mkdir -p $out/share/pointers-utility
            find . -name "interface.rrlib" -exec cp {} $out/share/pointers-utility/. \;
          '';
        };

        ace = let
          libDeps = [packages.pointersUtility];
          theories = pkgs.rocqPackages.mkRocqDerivation rec {
            inherit (ace) meta version;

            pname = "ace-theories";
            opam-name = "ace-theories";

            src = "${ACE-RISCV}/verification/theories";

            preBuild = ''
              find . -name "dune" -exec sed -i -e '3s|.*|  (package ace-theories)|g' {} \;
              cat << EOF > dune-project
              (lang dune 3.8)
              (using coq 0.8)
              (name ace-theories)
              (package (name ace-theories))
              EOF
            '';

            propagatedBuildInputs = [rrPackages.theories];
            useDune = true;
          };
        in pkgs.rocqPackages.mkRocqDerivation rec {
          inherit (ace) meta version;

          pname = "ace";
          opam-name = "ace";
          
          src = lib.cargoRefinedRust rec {
            inherit (ace) cargoExtraArgs cargoVendorDir doCheck meta src version;
            inherit libDeps pname target;

            cargoArtifacts = toolchain.envBuilder.buildDepsOnly {
              inherit (ace) cargoExtraArgs cargoVendorDir doCheck meta src version;
              inherit pname;
            };

            preBuild = ''
              sed -i -e '15i#![rr::package("ace")]' ./src/lib.rs
              sed -i -e '16i#![rr::import("ace.theories.base", "base")]' ./src/lib.rs
              cp --no-preserve=mode -r ${ACE-RISCV}/verification/{RefinedRust.toml,extra_specs.v,rust_proofs} .
            '';

            INSTALL_DIR = packages.opensbi;
            LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];
          };

          propagatedBuildInputs = libDeps ++ [rrPackages.stdlib theories];
          useDune = true;

          passthru = {inherit src;};

          postInstall = ''
            mkdir -p $out/share/ace
            find . -name "interface.rrlib" -exec cp {} $out/share/ace/. \;
          '';
        };

        default = packages.ace;
      };

      formatter = pkgs.alejandra;
    });
}
