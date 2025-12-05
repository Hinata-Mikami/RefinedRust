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
      inherit (lib) pkgs rrPkgs;
      lib = refinedrust.lib.${localSystem};

      crossSystem = "riscv64-linux";
      target = "riscv64gc-unknown-none-elf";

      crossPkgs = import refinedrust.inputs.nixpkgs {
        inherit localSystem crossSystem;
      };

      toolchain = rrPkgs."target-${target}".passthru.toolchain;
      envBuilder = lib.rust.overrideToolchain toolchain;

      ace = rec {
        version = "0.4.0";
        src = "${ACE-RISCV}/security-monitor";

        meta = with pkgs.lib; {
          homepage = "https://github.com/IBM/ACE-RISCV";
          license = licenses.asl20;
        };

        doCheck = false;
        cargoExtraArgs = "-Zbuild-std=core,alloc --target=${target}";
        cargoVendorDir = envBuilder.vendorMultipleCargoDeps {
          inherit (envBuilder.findCargoFiles src) cargoConfigs;

          cargoLockList = [
            "${src}/Cargo.lock"
            "${toolchain.passthru.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
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

          src = lib.rust.cargoRefinedRust rec {
            inherit (ace) cargoVendorDir doCheck meta src version;
            inherit pname target;

            cargoExtraArgs = ace.cargoExtraArgs + " --package pointers_utility";

            cargoArtifacts = envBuilder.buildDepsOnly {
              inherit (ace) cargoVendorDir doCheck meta src version;
              inherit cargoExtraArgs pname;
            };

            preBuild = ''
              sed -i -e '11i#![rr::package("pointers-utility")]' ./rust-crates/pointers_utility/src/lib.rs
              cp --no-preserve=mode -r ${ACE-RISCV}/verification/{RefinedRust.toml,extra_specs.v,rust_proofs} .
            '';
          };

          propagatedBuildInputs = [rrPkgs.stdlib];
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

            propagatedBuildInputs = [rrPkgs.theories];
            useDune = true;
          };
        in
          pkgs.rocqPackages.mkRocqDerivation rec {
            inherit (ace) meta version;

            pname = "ace";
            opam-name = "ace";

            src = lib.rust.cargoRefinedRust rec {
              inherit (ace) cargoExtraArgs cargoVendorDir doCheck meta src version;
              inherit libDeps pname target;

              cargoArtifacts = envBuilder.buildDepsOnly {
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

            propagatedBuildInputs = libDeps ++ [rrPkgs.stdlib theories];
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
