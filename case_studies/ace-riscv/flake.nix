{
  inputs = {
    refinedrust.url = "git+file://../../..";

    nixpkgs.follows = "refinedrust/nixpkgs";
    flake-parts.follows = "refinedrust/flake-parts";

    ACE-RISCV = {
      url = "github:IBM/ACE-RISCV?ref=refinedrust-main";
      flake = false;
    };
  };

  outputs = inputs @ {
    ACE-RISCV,
    flake-parts,
    nixpkgs,
    self,
    refinedrust,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        lib,
        pkgs,
        system,
        ...
      }: let
        rrPkgs = refinedrust.packages.${system};
        rrLib = refinedrust.lib;

        crossSystem = "riscv64-linux";
        target = "riscv64gc-unknown-none-elf";

        crossPkgs = import nixpkgs {
          inherit crossSystem;
          localSystem = system;
        };

        toolchain = rrLib.rust.mkToolchain pkgs rrPkgs.default.passthru.channel ["cargo" "llvm-tools-preview" "rustc" "rustc-dev" "rust-src"];
        envBuilder = rrLib.rust.overrideToolchain pkgs toolchain;

        ace = rec {
          version = "0.4.0";
          src = "${ACE-RISCV}/security-monitor";

          meta = with pkgs.lib; {
            homepage = "https://github.com/IBM/ACE-RISCV";
            license = licenses.asl20;
          };

          cargoExtraArgs = "-Zbuild-std=core,alloc --target=${target}";
          cargoVendorDir = envBuilder.vendorMultipleCargoDeps {
            inherit (envBuilder.findCargoFiles src) cargoConfigs;

            cargoLockList = [
              "${src}/Cargo.lock"
              "${toolchain.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
            ];
          };
        };

        prunedAceProofModules = let
          modules = builtins.getEnv "ACE_PRUNED_MODULES";
        in
          if modules != ""
          then builtins.filter (m: m != "") (pkgs.lib.splitString " " modules)
          else [];
      in rec {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [refinedrust.overlays.default];
        };

        packages = {
          opensbi = crossPkgs.opensbi.overrideAttrs (prev: rec {
            version = "92e8affb31b21ddc5d1193cf754ce644db7b460a";

            nativeBuildInputs = (prev.nativeBuildInputs or []) ++ [pkgs.coreutils];

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
              "READLINK=${pkgs.coreutils}/bin/readlink"
            ];

            installFlags = ["I=$(out)/opensbi-rust-bindings"];

            postInstall = ''
              ln -s $out/opensbi-rust-bindings/{lib64,lib}
            '';
          });

          pointersUtility = rrLib.rocq.mkRefinedRust pkgs rrPkgs.frontend rrPkgs.stdlib rec {
            inherit (ace) cargoVendorDir meta src version;

            doCheck = false;
            pname = "pointers-utility";

            cargoExtraArgs = ace.cargoExtraArgs + " --package pointers_utility";
            cargoArtifacts = envBuilder.buildDepsOnly {
              inherit (ace) cargoVendorDir meta src version;
              inherit cargoExtraArgs doCheck pname;
            };

            cargoRefinedRustArgs = {
              inherit toolchain;

              preBuild = ''
                sed -i -e '11i#![rr::package("pointers-utility")]' ./rust-crates/pointers_utility/src/lib.rs
                cp --no-preserve=mode -r ${ACE-RISCV}/verification/{RefinedRust.toml,extra_specs.v,rust_proofs} .
              '';
            };
          };

          ace = rrLib.rocq.mkRefinedRust pkgs rrPkgs.frontend rrPkgs.stdlib rec {
            inherit (ace) cargoExtraArgs cargoVendorDir meta src version;

            pname = "ace";
            libDeps = [packages.pointersUtility];

            doCheck = false;
            cargoArtifacts = envBuilder.buildDepsOnly {
              inherit cargoExtraArgs cargoVendorDir doCheck pname meta src version;
            };
            withTheories = true;

            cargoRefinedRustArgs = {
              inherit toolchain;

              preBuild = ''
                sed -i -e '15i#![rr::package("ace")]' ./src/lib.rs
                sed -i -e '16i#![rr::import("ace.theories.base", "base")]' ./src/lib.rs
                cp --no-preserve=mode -r ${ACE-RISCV}/verification/{RefinedRust.toml,extra_specs.v,rust_proofs} .
              '';

              INSTALL_DIR = packages.opensbi;
              LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];
            };

            rocqTheoriesArgs = {
              src = "${ACE-RISCV}/verification/theories";

              preBuild = ''
                find . -name "dune" -exec sed -i -e '1s|.*|(rocq.theory|g' {} \;
                find . -name "dune" -exec sed -i -e '3s|.*|  (package ace-theories)|g' {} \;
                cat << EOF > dune-project
                (lang dune 3.21)
                (using rocq 0.11)
                (name ace-theories)
                (package (name ace-theories))
                EOF
              '';
            };
          };

          ace-ci = packages.ace.overrideAttrs (prev: {
            preBuild = ''
              dune() { command dune "$@" --display=short; }
              echo "[ace-ci] Pruning dune modules from ace/proofs/dune"
              echo "[ace-ci] Modules to remove (${toString (builtins.length prunedAceProofModules)}): ${pkgs.lib.concatStringsSep ", " prunedAceProofModules}"
              ${pkgs.python3}/bin/python3 ${ACE-RISCV}/.github/workflows/prune_dune_modules.py ace/proofs/dune ${pkgs.lib.concatStringsSep " " prunedAceProofModules}
            '';
          });

          default = packages.ace;
        };

        formatter = pkgs.alejandra;
      };
    };
}
