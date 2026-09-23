{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-26.05";
    flake-parts.url = "github:hercules-ci/flake-parts";

    crane.url = "github:ipetkov/crane";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    Sniper = {
      url = "github:SMTCoq/Sniper";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-parts.follows = "flake-parts";
      };
    };

    verit = {
      url = "git+https://gitlab.mpi-sws.org/lgaeher/verit?rev=6348b82f16c7cd2eb2a0b8f2b48d3f35cbb62b90";
      flake = false;
    };
  };

  outputs =
    inputs@{
      crane,
      flake-parts,
      nixpkgs,
      rust-overlay,
      self,
      Sniper,
      verit,
      ...
    }:
    let
      name = "refinedrust";
      version = "0.1.0";

      meta = {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = nixpkgs.lib.licenses.bsd3;
      };

      pins = {
        equations = {
          version = "c4e99d8953cee0396a391fe017204bbc2af1fb88";
          sha256 = "sha256-4uhcYRwZxcSRDQgJ92D854djy76piuVhttDe6XEN0Rk=";
        };

        stdpp = {
          version = "729c671ed573749588f699138e306dbae880f3e1";
          sha256 = "sha256-cFUimy54xl4zA9q7NadjReAspRZPrh0DSdEpTJFPidU=";
        };

        iris = {
          version = "4a6add171278417fec6da7c490fe487e502326f0";
          sha256 = "sha256-4XY7u6KOMPENIiM/RlhOKKf06ABfnAVE8TJEeNHhn78=";
        };

        iris-contrib = {
          version = "0ed8e45b554b2c7f7b9102818bc3ee27d8fa18b8";
          sha256 = "sha256-Y9HyQvCnX9elwDSWK8o2Sh3E6nIRkaIxvD/zNo25Lxw=";
        };

        lambda-rust = {
          version = "0a062fb1eb68f9a6ac38412347117b294fc7746b";
          sha256 = "sha256-iQqxhPMSo/ktfhANwFlDV1Vpl4yWr9k0s/t2tFFAkpo=";
        };

        smtcoq = {
          version = "6de39db2a996cdc663634cb79193b9d75f95b48a";
          sha256 = "sha256-adhKClONIp3tltToQcoDO1wfqGzBCe/UE/WyBIPYlis=";
        };

        verit = {
          version = "6348b82f16c7cd2eb2a0b8f2b48d3f35cbb62b90";
          src = verit;
        };

        sniper = {
          version = "14fd1f02104f6e1214ad436d21eaacfb0d71db19";
          sha256 = "sha256-bFjwYVVP2/SNixSrThp3c8RYrmSmLb7NdjzpNtcDyAk=";
        };
      };

      stdlib = stdlibPkgs: [
        {
          pname = "stdlib-alloc";
          src = ./stdlib/alloc;
          libDeps = with stdlibPkgs; [
            stdlib-ptr
            stdlib-result
            stdlib-clone
            stdlib-mem
            stdlib-closures
          ];
        }
        {
          pname = "stdlib-arithops";
          src = ./stdlib/arithops;
        }
        {
          pname = "stdlib-boxed";
          src = ./stdlib/boxed;
          libDeps = with stdlibPkgs; [
            stdlib-alloc
            stdlib-option
            stdlib-mem
            stdlib-ptr
            stdlib-rr_internal
            stdlib-ptr-advanced
          ];
        }
        {
          pname = "stdlib-btreemap";
          src = ./stdlib/btreemap;
          libDeps = with stdlibPkgs; [
            stdlib-alloc
            stdlib-option
            stdlib-clone
            stdlib-cmp
          ];
        }
        {
          pname = "stdlib-clone";
          src = ./stdlib/clone;
          libDeps = with stdlibPkgs; [ stdlib-sized ];
        }
        {
          pname = "stdlib-closures";
          src = ./stdlib/closures;
        }
        {
          pname = "stdlib-cmp";
          src = ./stdlib/cmp;
          libDeps = with stdlibPkgs; [
            stdlib-closures
            stdlib-option
          ];
        }
        {
          pname = "stdlib-controlflow";
          src = ./stdlib/controlflow;
          libDeps = with stdlibPkgs; [
            stdlib-option
            stdlib-result
          ];
        }
        {
          pname = "stdlib-iterator";
          src = ./stdlib/iterator;
          libDeps = with stdlibPkgs; [
            stdlib-clone
            stdlib-closures
            stdlib-cmp
            stdlib-option
            stdlib-range
            stdlib-result
            stdlib-controlflow
          ];
        }
        {
          pname = "stdlib-sized";
          src = ./stdlib/sized;
        }
        {
          pname = "stdlib-index";
          src = ./stdlib/index;
          libDeps = with stdlibPkgs; [ stdlib-sized ];
        }
        {
          pname = "stdlib-mem";
          src = ./stdlib/mem;
        }
        {
          pname = "stdlib-option";
          src = ./stdlib/option;
          libDeps = with stdlibPkgs; [
            stdlib-closures
            stdlib-clone
            stdlib-result
          ];
        }
        {
          pname = "stdlib-ptr";
          src = ./stdlib/ptr;
          libDeps = with stdlibPkgs; [
            stdlib-mem
            stdlib-clone
            stdlib-num
            stdlib-option
          ];
        }
        {
          pname = "stdlib-ptr-advanced";
          src = ./stdlib/ptr_advanced;
          libDeps = with stdlibPkgs; [
            stdlib-mem
            stdlib-ptr
            stdlib-option
            stdlib-clone
          ];
        }
        {
          pname = "stdlib-result";
          src = ./stdlib/result;
          libDeps = with stdlibPkgs; [
            stdlib-clone
            stdlib-closures
          ];
        }
        {
          pname = "stdlib-range";
          src = ./stdlib/range;
          libDeps = with stdlibPkgs; [
            stdlib-cmp
            stdlib-option
          ];
        }
        {
          pname = "stdlib-rr_internal";
          src = ./stdlib/rr_internal;
          libDeps = with stdlibPkgs; [
            stdlib-alloc
            stdlib-ptr
          ];
        }
        {
          pname = "stdlib-rwlock";
          src = ./stdlib/rwlock;
        }
        {
          pname = "stdlib-num";
          src = ./stdlib/num;
        }
        {
          pname = "stdlib-cell";
          src = ./stdlib/cell;
          libDeps = with stdlibPkgs; [
            stdlib-sized
          ];
        }
        {
          pname = "stdlib-spin";
          src = ./stdlib/spin;
          libDeps = with stdlibPkgs; [
            stdlib-option
            stdlib-cell
            stdlib-closures
            stdlib-arithops
          ];
        }
        {
          pname = "stdlib-vec";
          src = ./stdlib/vec;
          libDeps = with stdlibPkgs; [
            stdlib-alloc
            stdlib-iterator
            stdlib-option
            stdlib-rr_internal
            stdlib-closures
            stdlib-index
            stdlib-cmp
            stdlib-ptr-advanced
            stdlib-clone
            stdlib-controlflow
          ];
        }
        {
          pname = "stdlib-stdlib";
          opam-name = "refinedrust-stdlib";
          src = ./stdlib/stdlib;
          libDeps = builtins.attrValues (builtins.removeAttrs stdlibPkgs [ "stdlib-stdlib" ]);
        }
      ];

      case_studies = [
        {
          pname = "evenint";
          src = ./case_studies/evenint;
        }
        {
          pname = "hillel";
          src = ./case_studies/hillel;
        }
        {
          pname = "minivec";
          src = ./case_studies/minivec;
        }
        {
          pname = "minicell";
          src = ./case_studies/minicell;
        }
        {
          pname = "linkedlist";
          src = ./case_studies/linkedlist;
        }
        {
          pname = "paper-examples";
          src = ./case_studies/paper_examples;
        }
        {
          pname = "iterators";
          src = ./case_studies/iterators;
        }
        {
          pname = "knights-tour";
          src = ./case_studies/knights_tour;
        }
        {
          pname = "knights-tour-functional";
          src = ./case_studies/knights_tour_functional;
        }
        {
          pname = "tests";
          src = ./case_studies/tests;
        }
        {
          pname = "smtcoq";
          src = ./case_studies/smtcoq;
        }
        {
          pname = "verifythis2026";
          src = ./case_studies/verifythis2026;
        }
      ];
    in
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];

      flake = {
        lib = import ./nix { inherit crane nixpkgs rust-overlay; };

        overlays = {
          deps = import ./nix/deps pins;

          default = nixpkgs.lib.composeManyExtensions [
            rust-overlay.overlays.default
            Sniper.overlays.default
            self.overlays.deps
          ];
        };
      };

      perSystem =
        {
          lib,
          pkgs,
          system,
          ...
        }:
        let
          rust =
            let
              inherit (toolchainFile) channel components;
              toolchainFile = (lib.importTOML ./rr_frontend/rust-toolchain.toml).toolchain;
              devComponents = [
                "clippy"
                "rust-analyzer"
                "rust-src"
                "rustfmt"
              ];
            in
            rec {
              toolchain = rec {
                inherit channel;

                build = self.lib.rust.mkToolchain pkgs channel components;
                dev = self.lib.rust.mkToolchain pkgs channel (components ++ devComponents);
              };

              envBuilder = self.lib.rust.overrideToolchain pkgs toolchain.build;
            };
        in
        rec {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };

          packages =
            let
              mkStdlib =
                {
                  pname,
                  opam-name ? pname,
                  ...
                }@origArgs:
                let
                  args = builtins.removeAttrs origArgs [
                    "pname"
                    "opam-name"
                  ];
                in
                self.lib.rocq.mkRefinedRust pkgs packages.frontend packages.stdlib (
                  {
                    inherit meta version;

                    inherit pname opam-name;

                    withStdlib = false;
                    generateFiles = false;
                    useDune = true;
                    propagatedBuildInputs = [ packages.refinedrust-smtcoq ];

                    preBuild = ''
                      find . -name dune -exec sed -i -e 's/(package refinedrust-stdlib)/(package ${opam-name})/g' {} \;
                      cat << EOF > dune-project
                      (lang dune 3.21)
                      (using rocq 0.11)
                      (name ${opam-name})
                      (package (name ${opam-name}))
                      EOF
                    '';
                  }
                  // args
                );
            in
            {
              refinedrust = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = name;
                opam-name = name;
                src = ./theories;

                propagatedBuildInputs = [
                  pkgs.rocqPackages.equations
                  pkgs.rocqPackages.iris-contrib
                  pkgs.rocqPackages.lambda-rust
                ];
                useDune = true;
              };

              refinedrust-smtcoq = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = name + "-smtcoq";
                opam-name = name + "-smtcoq";
                src = ./theories;

                propagatedBuildInputs = [
                  packages.refinedrust
                  pkgs.rocqPackages.sniper
                ];
                useDune = true;
              };

              frontend = rust.envBuilder.buildPackage rec {
                inherit meta version;

                pname = "cargo-${name}";
                src = ./rr_frontend;

                cargoArtifacts = rust.envBuilder.buildDepsOnly {
                  inherit
                    meta
                    pname
                    src
                    version
                    ;
                };

                nativeBuildInputs =
                  with pkgs;
                  [ makeWrapper ]
                  ++ (lib.optionals stdenv.isDarwin [
                    libiconv
                    libzip
                  ]);

                postInstall = ''
                  wrapProgram $out/bin/${pname} \
                    --set-default LD_LIBRARY_PATH ${rust.toolchain.build}/lib \
                    --set-default DYLD_FALLBACK_LIBRARY_PATH ${rust.toolchain.build}/lib
                '';

                doNotRemoveReferencesToRustToolchain = true;
                passthru = { inherit cargoArtifacts pname src; };
              };

              default =
                let
                  mkRefinedRust =
                    toolchain:
                    pkgs.symlinkJoin {
                      inherit meta name;

                      paths = [
                        pkgs.gcc
                        packages.frontend
                        toolchain
                        (self.lib.mkDuneWrapper pkgs packages.stdlib)
                      ];

                      nativeBuildInputs = [ pkgs.makeWrapper ];
                      postBuild = ''
                        wrapProgram $out/bin/cargo-${name} \
                          --set LD_LIBRARY_PATH ${toolchain}/lib \
                          --set DYLD_FALLBACK_LIBRARY_PATH ${toolchain}/lib \
                          --set PATH "$out/bin" \
                          --set RR_NIX_STDLIB $out/share
                      '';

                      passthru = {
                        inherit (rust.toolchain) channel;
                        inherit mkRefinedRust;
                      };
                    };
                in
                mkRefinedRust rust.toolchain.build;

              stdlib = packages.stdlib-stdlib;

              devcontainer =
                let
                  cargoVendorDir = rust.envBuilder.vendorMultipleCargoDeps {
                    inherit (rust.envBuilder.findCargoFiles ./rr_frontend) cargoConfigs;

                    cargoLockList = [
                      ./rr_frontend/Cargo.lock
                      "${rust.toolchain.dev.availableComponents.rust-src}/lib/rustlib/src/rust/library/Cargo.lock"
                    ];
                  };
                in
                self.lib.mkDevContainer pkgs [
                  pkgs.gcc
                  pkgs.gnumake
                  rust.toolchain.dev
                  cargoVendorDir
                  (self.lib.mkDuneWrapper pkgs packages.refinedrust-smtcoq)
                ] rust.toolchain.dev;
            }
            // lib.fix (f: self.lib.mapToAttrs mkStdlib (stdlib f));

          checks =
            let
              mkCaseStudies =
                let
                  extraProofs = pkgs.rocqPackages.mkRocqDerivation rec {
                    inherit meta version;

                    pname = "extra-proofs";
                    opam-name = "extra-proofs";

                    src = ./case_studies/extra_proofs;

                    buildInputs = [ packages.refinedrust-smtcoq ];
                    useDune = true;
                  };
                in
                args:
                self.lib.rocq.mkRefinedRust pkgs packages.frontend packages.stdlib (
                  {
                    inherit meta version;

                    propagatedBuildInputs = [ extraProofs ];

                    cargoArtifacts = null;
                    cargoExtraArgs = "";
                    cargoVendorDir = null;

                    cargoRefinedRustArgs = {
                      toolchain = rust.toolchain.build;
                    };
                  }
                  // args
                );
            in
            {
              clippy = self.lib.rust.cargoClippy pkgs rust.toolchain.dev {
                inherit (packages.frontend.passthru) cargoArtifacts pname src;

                cargoClippyExtraArgs = "--all-targets --all-features --no-deps";
              };

              deny = self.lib.rust.cargoDeny pkgs {
                inherit (packages.frontend.passthru) pname src;
              };

              fmt = self.lib.rust.cargoFmt pkgs rust.toolchain.dev {
                inherit (packages.frontend.passthru) pname src;
              };

              machete = self.lib.rust.cargoMachete pkgs {
                inherit (packages.frontend.passthru) pname src;
              };

              workspace-unused = self.lib.rust.cargoWorkspaceUnused pkgs rust.toolchain.dev {
                inherit (packages.frontend.passthru) pname src;
              };
            }
            // self.lib.mapToAttrs mkCaseStudies case_studies;

          devShells.default = pkgs.mkShell {
            inputsFrom = with packages; [
              frontend
              refinedrust
            ];

            packages = with pkgs; [
              cargo-deny
              cargo-machete
              gnumake
              rust.toolchain.dev
              pkgs.rocqPackages.sniper
            ];

            LD_LIBRARY_PATH = lib.makeLibraryPath [ rust.toolchain.dev ];
            DYLD_FALLBACK_LIBRARY_PATH = lib.makeLibraryPath [ rust.toolchain.dev ];
            LIBCLANG_PATH = lib.makeLibraryPath [ pkgs.libclang.lib ];
          };

          formatter = pkgs.nixfmt-tree;
        };
    };
}
