{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";

    crane.url = "github:ipetkov/crane";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    rust-targets = {
      url = "file+https://raw.githubusercontent.com/oxalica/rust-overlay/refs/heads/master/manifests/targets.nix";
      flake = false;
    };
  };

  outputs = {
    self,
    crane,
    flake-utils,
    nixpkgs,
    rust-overlay,
    rust-targets,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      lib = nixpkgs.lib.extend (_: _: (import ./nix {
        inherit self pkgs system;
        craneLib = rust.lib.craneLib;
      }));

      overlays = [lib.overlays.ocamlFlambda rust-overlay.overlays.default];
      pkgs = import nixpkgs {inherit overlays system;};

      name = "refinedrust";
      version = "0.1.0";

      meta = with pkgs.lib; {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = licenses.bsd3;
      };

      ocaml = {
        version = pkgs.ocaml.version;
      };

      rocq = {
        version = pkgs.rocqPackages.rocq-core.rocq-version;

        stdpp = {
          version = "ec795ece9125d60d9974e15fc52f3dfe91ae3f4b";
          sha256 = "sha256-vtPP8K64MvweX5oUY4ka5ReeDim76FEv2gUvm941nj0=";
        };

        iris = {
          version = "6b080cdd7a145cd5cbb2b7d8b17adf6ee2ca8f08";
          sha256 = "sha256-4gubzNiDLFc0R4UmpYCUHVOuhUmQkLHbWa1yloudPxc=";
        };

        iris-contrib = {
          version = "6c7ba2fb49b0849ebc6c4476e1d11ffce534d4fd";
          sha256 = "sha256-pxd8VK8z5kWEam3t5DmXOQECDt4/BWKbUicesFkM6qw=";
        };

        lambda-rust = {
          version = "8e401c363dc8e4337afcadce832e0cef9dc33a7c";
          sha256 = "sha256-D+MKk8MkP9MYgK9Gwrmc1IN7a8AUEXSzAk/pLinpEtg=";
        };
      };

      rust = with pkgs.lib; let
        availableTargets = attrsets.attrValues (import rust-targets.outPath);
        inputsToolchain = (importTOML ./rr_frontend/rust-toolchain.toml).toolchain;
        devComponents = ["clippy" "rust-analyzer" "rust-src" "rustfmt"];
      in {
        lib = rec {
          inherit (craneLib) cargoDeny;
          inherit (lib) cargoMachete cargoRefinedRust;

          craneLib = crane.mkLib pkgs;
          cargoClippy = craneLib.cargoClippy.override {clippy = rust.toolchain.dev;};
          cargoFmt = craneLib.cargoFmt.override {rustfmt = rust.toolchain.dev;};
        };

        hostPlatform = pkgs.stdenv.hostPlatform.rust.rustcTarget;
        toolchain = rust.mkToolchain rust.hostPlatform;

        mkToolchain = target: let
          addRustSrc =
            attrsets.optionalAttrs (target != rust.hostPlatform) {extensions = ["rust-src"];};
        in rec {
          build = (pkgs.rust-bin.fromRustupToolchain inputsToolchain // {targets = [target];}).override addRustSrc;
          dev = build.override {extensions = inputsToolchain.components ++ devComponents;};
          envBuilder = rust.lib.craneLib.overrideToolchain build;
        };

        mkTargetToolchains = drv:
          listToAttrs (map (target: {
              name = "target-" + target;
              value = drv (rust.mkToolchain target);
            })
            availableTargets);
      };
    in
      with pkgs.lib; rec {
        inherit lib;

        packages =
          {
            theories = let
              # NOTE: Remove `equations` when available in Nix's `RocqPackages`
              equations = pkgs.rocqPackages.mkRocqDerivation {
                pname = "equations";
                owner = "mattam82";
                repo = "Coq-Equations";
                opam-name = "rocq-equations";

                propagatedBuildInputs = [pkgs.rocqPackages.stdlib pkgs.ocamlPackages.ppx_optcomp];

                mlPlugin = true;
                useDune = true;

                version = "2ce6d98dd03979369d739ac139db4da4f7eab352";
                release = {
                  "2ce6d98dd03979369d739ac139db4da4f7eab352".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
                };
              };

              stdpp = lib.mkDepRocqDerivation rocq.stdpp {
                pname = "stdpp";
              };

              iris = lib.mkDepRocqDerivation rocq.iris {
                pname = "iris";
                propagatedBuildInputs = [stdpp];
              };

              iris-contrib = lib.mkDepRocqDerivation rocq.iris-contrib {
                pname = "iris-contrib";
                propagatedBuildInputs = [iris];
              };

              lambda-rust = lib.mkDepRocqDerivation rocq.lambda-rust {
                pname = "lambda-rust";
                propagatedBuildInputs = [iris];
              };
            in
              pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = name;
                opam-name = name;
                src = ./theories;

                propagatedBuildInputs = [equations iris-contrib lambda-rust];
                useDune = true;
              };

            frontend = rust.toolchain.envBuilder.buildPackage rec {
              inherit meta version;

              pname = "cargo-${name}";
              src = ./rr_frontend;

              cargoArtifacts = rust.toolchain.envBuilder.buildDepsOnly {
                inherit meta pname src version;
              };

              nativeBuildInputs = with pkgs;
                lib.optionals stdenv.isDarwin [libiconv libzip];

              doNotRemoveReferencesToRustToolchain = true;
              passthru = {inherit cargoArtifacts pname src;};
            };

            stdlib = pkgs.rocqPackages.mkRocqDerivation {
              inherit meta version;

              pname = "refinedrust-stdlib";
              opam-name = "refinedrust-stdlib";
              src = ./stdlib;

              buildInputs = [packages.frontend rust.toolchain.build];
              propagatedBuildInputs = [packages.theories];

              configurePhase = "make generate_stdlib";
              useDune = true;
            };

            closures = pkgs.rocqPackages.mkRocqDerivation {
              inherit meta version;

              pname = "stdlib-closures";
              opam-name = "stdlib-closures";

              src = rust.lib.cargoRefinedRust {
                inherit meta version;

                pname = "stdlib-closures";
                src = ./stdlib/closures;

                cargoArtifacts = null;
                withStdlib = false;
              };

              propagatedBuildInputs = [packages.theories];
              useDune = true;

              postInstall = ''
                mkdir -p $out/share/refinedrust-stdlib/closures
                find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/closures/. \;
              '';
            };

            arithops = pkgs.rocqPackages.mkRocqDerivation {
              inherit meta version;

              pname = "stdlib-arithops";
              opam-name = "stdlib-arithops";

              src = rust.lib.cargoRefinedRust {
                inherit meta version;

                pname = "stdlib-arithops";
                src = ./stdlib/arithops;

                cargoArtifacts = null;
                withStdlib = false;
              };

              propagatedBuildInputs = [packages.theories];
              useDune = true;

              postInstall = ''
                mkdir -p $out/share/refinedrust-stdlib/arithops
                find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/arithops/. \;
              '';
            };

            mem = let
              theories = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-mem-theories";
                opam-name = "stdlib-mem-theories";

                src = ./stdlib/mem/theories;

                propagatedBuildInputs = [packages.theories];
                useDune = true;
              };
            in
              pkgs.rocqPackages.mkRocqDerivation rec {
                inherit meta version;

                pname = "stdlib-mem";
                opam-name = "stdlib-mem";

                src = rust.lib.cargoRefinedRust {
                  inherit meta version;

                  pname = "stdlib-mem";
                  src = ./stdlib/mem;

                  cargoArtifacts = null;
                  withStdlib = false;
                };

                propagatedBuildInputs = [packages.theories theories];
                useDune = true;

                postInstall = ''
                  mkdir -p $out/share/refinedrust-stdlib/mem
                  find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/mem/. \;
                '';

                passthru = {inherit src;};
              };

            ptr = let
              theories = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-ptr-theories";
                opam-name = "stdlib-ptr-theories";

                src = ./stdlib/ptr/theories;

                propagatedBuildInputs = [packages.theories];
                useDune = true;
              };
            in
              pkgs.rocqPackages.mkRocqDerivation rec {
                inherit meta version;

                pname = "stdlib-ptr";
                opam-name = "stdlib-ptr";

                src = rust.lib.cargoRefinedRust {
                  inherit meta version;

                  pname = "stdlib-ptr";
                  src = ./stdlib/ptr;

                  cargoArtifacts = null;
                  withStdlib = false;

                  RR_LIB_LOAD_PATHS = pkgs.lib.makeSearchPathOutput "" "" [packages.mem];
                };

                propagatedBuildInputs = [packages.theories theories packages.mem];
                useDune = true;

                postInstall = ''
                  mkdir -p $out/share/refinedrust-stdlib/ptr
                  find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/ptr/. \;
                '';

                passthru = {inherit src;};
              };

            result = let
              theories = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-result-theories";
                opam-name = "stdlib-result-theories";

                src = ./stdlib/result/theories;

                propagatedBuildInputs = [packages.theories];
                useDune = true;
              };
            in
              pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-result";
                opam-name = "stdlib-result";

                src = rust.lib.cargoRefinedRust {
                  inherit meta version;

                  pname = "stdlib-result";
                  src = ./stdlib/result;

                  cargoArtifacts = null;
                  withStdlib = false;
                };

                propagatedBuildInputs = [packages.theories theories];
                useDune = true;

                postInstall = ''
                  mkdir -p $out/share/refinedrust-stdlib/result
                  find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/result/. \;
                '';
              };

            option = pkgs.rocqPackages.mkRocqDerivation rec {
              inherit meta version;

              pname = "stdlib-option";
              opam-name = "stdlib-option";

              src = rust.lib.cargoRefinedRust {
                inherit meta version;

                pname = "stdlib-option";
                src = ./stdlib/option;

                cargoArtifacts = null;
                withStdlib = false;
              };

              propagatedBuildInputs = [packages.theories];
              useDune = true;
              postInstall = ''
                mkdir -p $out/share/refinedrust-stdlib/option
                find ${src} -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/option/. \;
              '';
            };

            clone = pkgs.rocqPackages.mkRocqDerivation rec {
              inherit meta version;

              pname = "stdlib-clone";
              opam-name = "stdlib-clone";

              src = rust.lib.cargoRefinedRust {
                inherit meta version;

                pname = "stdlib-clone";
                src = ./stdlib/clone;

                cargoArtifacts = null;
                withStdlib = false;
              };

              propagatedBuildInputs = [packages.theories];
              useDune = true;
              postInstall = ''
                mkdir -p $out/share/refinedrust-stdlib/clone
                find ${src} -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/clone/. \;
              '';
            };

            controlflow = pkgs.rocqPackages.mkRocqDerivation rec {
              inherit meta version;

              pname = "stdlib-controlflow";
              opam-name = "stdlib-controlflow";

              src = rust.lib.cargoRefinedRust {
                inherit meta version;

                pname = "stdlib-controlflow";
                src = ./stdlib/controlflow;

                cargoArtifacts = null;
                withStdlib = false;

                RR_LIB_LOAD_PATHS = pkgs.lib.makeSearchPathOutput "" "" [packages.option packages.result];
              };

              propagatedBuildInputs = [packages.theories packages.option packages.result];
              useDune = true;

              patchPhase = ''
                sed -i -e 's/))/ rrstd.result.theories))/g' controlflow/generated/dune
              '';

              postInstall = ''
                mkdir -p $out/share/refinedrust-stdlib/controlflow
                find ${src} -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/controlflow/. \;
              '';
            };

            alloc = let
              theories = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-alloc-theories";
                opam-name = "stdlib-alloc-theories";

                src = ./stdlib/alloc/theories;

                propagatedBuildInputs = [packages.theories packages.ptr packages.mem];
                useDune = true;
              };
            in
              pkgs.rocqPackages.mkRocqDerivation rec {
                inherit meta version;

                pname = "stdlib-alloc";
                opam-name = "stdlib-alloc";

                src = rust.lib.cargoRefinedRust {
                  inherit meta version;

                  pname = "stdlib-alloc";
                  src = ./stdlib/alloc;

                  cargoArtifacts = null;
                  withStdlib = false;

                  RR_LIB_LOAD_PATHS = pkgs.lib.makeSearchPathOutput "" "" [packages.mem packages.ptr packages.result];
                  RUST_LOG="debug";
                };

                propagatedBuildInputs = [packages.theories theories packages.mem packages.ptr packages.result];
                useDune = true;

                postInstall = ''
                  mkdir -p $out/share/refinedrust-stdlib/alloc
                  find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/alloc/. \;
                '';

                passthru = {inherit src theories;};
              };

            stdlibNew = pkgs.symlinkJoin {
              inherit meta version;

              pname = "refinedrust-stdlib";
              opam-name = "refinedrust-stdlib";
              paths = with packages; [closures arithops mem ptr result option clone controlflow alloc];
            };

            default = packages."target-${rust.hostPlatform}";
          }
          // (
            rust.mkTargetToolchains (toolchain:
              pkgs.symlinkJoin {
                inherit meta name;

                paths = [pkgs.rocqPackages.rocq-core packages.frontend toolchain.build pkgs.gnupatch] ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs;

                nativeBuildInputs = [pkgs.makeWrapper];

                postBuild = let
                  fetchRocqDeps = drv: lists.unique [drv] ++ flatten (map fetchRocqDeps drv.propagatedBuildInputs);
                in
                  with strings; ''
                    wrapProgram $out/bin/dune \
                      --set OCAMLPATH "${makeSearchPath "lib/ocaml/${ocaml.version}/site-lib" ([pkgs.rocqPackages.rocq-core] ++ (fetchRocqDeps packages.stdlib))}" \
                      --set ROCQPATH "${makeSearchPath "lib/coq/${rocq.version}/user-contrib" (fetchRocqDeps packages.stdlib)}"

                    wrapProgram $out/bin/cargo-${name} \
                      --set LD_LIBRARY_PATH "${makeLibraryPath [toolchain.build]}" \
                      --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [toolchain.build]}" \
                      --set PATH "$out/bin" \
                      --set RR_NIX_STDLIB "${packages.stdlib}"/share/refinedrust-stdlib/
                  '';

                passthru = {inherit toolchain;};
              })
          );

        checks = let
          extraProofs = pkgs.rocqPackages.mkRocqDerivation rec {
            inherit meta version;

            pname = "extra-proofs";
            opam-name = "extra-proofs";

            src = ./case_studies/extra_proofs;

            propagatedBuildInputs = [packages.stdlib];
            useDune = true;
          };
        in
          {
            clippy = rust.lib.cargoClippy {
              inherit (packages.frontend.passthru) cargoArtifacts pname src;

              cargoClippyExtraArgs = "--all-targets --all-features --no-deps";
            };

            deny = rust.lib.cargoDeny {
              inherit (packages.frontend.passthru) pname src;
            };

            fmt = rust.lib.cargoFmt {
              inherit (packages.frontend.passthru) pname src;
            };

            machete = rust.lib.cargoMachete {
              inherit (packages.frontend.passthru) pname src;
            };
          }
          // listToAttrs (map ({
              pname,
              src,
            }: {
              name = "case-study-" + pname;
              value = pkgs.rocqPackages.mkRocqDerivation {
                inherit meta pname version;

                opam-name = pname;
                src = rust.lib.cargoRefinedRust {
                  inherit meta pname src version;

                  cargoArtifacts = null;
                  cargoExtraArgs = "";
                  cargoVendorDir = null;
                };

                propagatedBuildInputs = [packages.stdlib extraProofs];
                useDune = true;
              };
            }) [
              {
                pname = "evenint";
                src = ./case_studies/evenint;
              }
              {
                pname = "minivec";
                src = ./case_studies/minivec;
              }
              {
                pname = "paper-examples";
                src = ./case_studies/paper_examples;
              }
              {
                pname = "paper-examples-rr20";
                src = ./case_studies/refinedrust-20-paper-examples;
              }
              {
                pname = "tests";
                src = ./case_studies/tests;
              }
            ]);

        devShells =
          {
            default = devShells."target-${rust.hostPlatform}";
          }
          // (
            rust.mkTargetToolchains (toolchain:
              pkgs.mkShell {
                inputsFrom = with packages; [frontend theories];
                packages = with pkgs; [cargo-deny cargo-machete gnumake gnupatch gnused toolchain.dev];

                LD_LIBRARY_PATH = makeLibraryPath [toolchain.dev];
                DYLD_FALLBACK_LIBRARY_PATH = makeLibraryPath [toolchain.dev];
                LIBCLANG_PATH = makeLibraryPath [pkgs.libclang.lib];
              })
          );

        formatter = pkgs.alejandra;
      });
}
