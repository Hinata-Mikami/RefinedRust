{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
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
    flake-utils,
    nixpkgs,
    rust-targets,
    ...
  } @ inputs:
    flake-utils.lib.eachDefaultSystem (system: let
      inherit (lib) pkgs;

      lib = nixpkgs.lib.extend (_: _: (import ./nix {
        inherit inputs system;
      }));

      name = "refinedrust";
      version = "0.1.0";

      meta = with pkgs.lib; {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = licenses.bsd3;
      };

      rocq = {
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

      rust = let
        inherit (toolchainFile) channel components;
        toolchainFile = (pkgs.lib.importTOML ./rr_frontend/rust-toolchain.toml).toolchain;
        devComponents = ["clippy" "rust-analyzer" "rust-src" "rustfmt"];
      in rec {
        toolchain = {
          build = lib.rust.mkToolchain channel components lib.rust.hostPlatform;
          dev = lib.rust.mkToolchain channel (components ++ devComponents) lib.rust.hostPlatform;
        };

        envBuilder = lib.rust.overrideToolchain toolchain.build;

        mkDrvRustTargetToolchains = drv:
          lib.mapToAttrs (targetName: "target-" + targetName) (targetName: drv (lib.rust.mkToolchain channel components targetName))
          (map (pname: {inherit pname;}) (pkgs.lib.attrsets.attrValues (import rust-targets.outPath)));
      };
    in
      with pkgs.lib; rec {
        inherit lib;

        packages =
          {
            theories = let
              stdpp = lib.rocq.mkDepDerivation rocq.stdpp {
                pname = "stdpp";
              };

              iris = lib.rocq.mkDepDerivation rocq.iris {
                pname = "iris";
                propagatedBuildInputs = [stdpp];
              };

              iris-contrib = lib.rocq.mkDepDerivation rocq.iris-contrib {
                pname = "iris-contrib";
                propagatedBuildInputs = [iris];
              };

              lambda-rust = lib.rocq.mkDepDerivation rocq.lambda-rust {
                pname = "lambda-rust";
                propagatedBuildInputs = [iris];
              };
            in
              pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = name;
                opam-name = name;
                src = ./theories;

                propagatedBuildInputs = [pkgs.rocqPackages.equations iris-contrib lambda-rust];
                useDune = true;
              };

            frontend = rust.envBuilder.buildPackage rec {
              inherit meta version;

              pname = "cargo-${name}";
              src = ./rr_frontend;

              cargoArtifacts = rust.envBuilder.buildDepsOnly {
                inherit meta pname src version;
              };

              nativeBuildInputs = with pkgs;
                lib.optionals stdenv.isDarwin [libiconv libzip];

              doNotRemoveReferencesToRustToolchain = true;
              passthru = {inherit cargoArtifacts pname src;};
            };

            alloc = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-alloc";
              src = ./stdlib/alloc;

              libDeps = [packages.ptr packages.result];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            arithops = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-arithops";
              src = ./stdlib/arithops;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            boxed = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-boxed";
              src = ./stdlib/boxed;

              libDeps = [packages.alloc packages.option packages.rr_internal];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            btreemap = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-btreemap";
              src = ./stdlib/btreemap;

              libDeps = [packages.alloc packages.option];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            clone = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-clone";
              src = ./stdlib/clone;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            closures = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-closures";
              src = ./stdlib/closures;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            cmp = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-cmp";
              src = ./stdlib/cmp;

              libDeps = [packages.closures packages.option];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            controlflow = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-controlflow";
              src = ./stdlib/controlflow;

              libDeps = [packages.option packages.result];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            iterator = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-iterator";
              src = ./stdlib/iterator;

              libDeps = [packages.clone packages.closures packages.cmp packages.option packages.range];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            mem = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-mem";
              src = ./stdlib/mem;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            option = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-option";
              src = ./stdlib/option;

              libDeps = [packages.closures];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            ptr = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-ptr";
              src = ./stdlib/ptr;

              libDeps = [packages.mem];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            result = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-result";
              src = ./stdlib/result;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            range = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-range";
              src = ./stdlib/range;

              libDeps = [packages.cmp packages.option];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            rr_internal = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-rr_internal";
              src = ./stdlib/rr_internal;

              libDeps = [packages.alloc packages.ptr];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;
            };

            rwlock = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-rwlock";
              src = ./stdlib/rwlock;

              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            spin = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-spin";
              src = ./stdlib/spin;

              libDeps = [packages.option];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
              withTheories = true;

              rocqTheoriesArgs = {
                pname = "stdlib-spin-once-theories";
                opam-name = "stdlib-spin-once-theories";

                src = ./stdlib/spin/theories/once;
              };
            };

            vec = lib.rocq.mkRefinedRust {
              inherit meta version;

              pname = "stdlib-vec";
              src = ./stdlib/vec;

              libDeps = [packages.alloc packages.iterator packages.option packages.rr_internal];
              propagatedBuildInputs = [packages.theories];

              cargoArtifacts = null;
              withStdlib = false;
            };

            stdlib = let
              libDeps = with packages; [alloc arithops boxed btreemap clone closures cmp controlflow iterator mem option ptr range result rr_internal rwlock spin vec];
            in
              pkgs.rocqPackages.mkRocqDerivation {
                inherit meta version;

                pname = "stdlib-refinedrust";
                opam-name = "stdlib-refinedrust";

                src = lib.rust.cargoRefinedRust rec {
                  inherit libDeps meta version;

                  pname = "stdlib-refinedrust";
                  src = ./stdlib/stdlib;

                  cargoArtifacts = null;
                  withStdlib = false;
                };

                propagatedBuildInputs = libDeps ++ [packages.theories];
                useDune = true;

                postInstall = ''
                  mkdir -p $out/share/refinedrust-stdlib/stdlib
                  find . -name "interface.rrlib" -exec cp {} $out/share/refinedrust-stdlib/stdlib/. \;
                '';
              };

            default = packages."target-${lib.rust.hostPlatform}";
          }
          // (
            rust.mkDrvRustTargetToolchains (toolchain:
              pkgs.symlinkJoin {
                inherit meta name;

                paths = [pkgs.rocqPackages.rocq-core packages.frontend toolchain pkgs.gnupatch] ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs;
                nativeBuildInputs = [pkgs.makeWrapper];

                postBuild = let
                  fetchRocqDeps = drv: lists.unique ([drv] ++ flatten (map fetchRocqDeps drv.propagatedBuildInputs));
                in
                  with strings; ''
                    wrapProgram $out/bin/dune \
                      --set OCAMLPATH "${makeSearchPath "lib/ocaml/${pkgs.ocaml.version}/site-lib" ([pkgs.rocqPackages.rocq-core] ++ (fetchRocqDeps packages.stdlib))}" \
                      --set ROCQPATH "${makeSearchPath "lib/coq/${pkgs.rocqPackages.rocq-core.rocq-version}/user-contrib" (fetchRocqDeps packages.stdlib)}"

                    wrapProgram $out/bin/cargo-${name} \
                      --set LD_LIBRARY_PATH "${makeLibraryPath [toolchain]}" \
                      --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [toolchain]}" \
                      --set PATH "$out/bin" \
                      --set RR_NIX_STDLIB "${packages.stdlib}"/share/refinedrust-stdlib/
                  '';

                passthru = {inherit toolchain;};
              })
          );

        checks = let
          mkCaseStudies = let
            extraProofs = pkgs.rocqPackages.mkRocqDerivation rec {
              inherit meta version;

              pname = "extra-proofs";
              opam-name = "extra-proofs";

              src = ./case_studies/extra_proofs;

              buildInputs = [packages.theories];
              useDune = true;
            };
          in
            {
              pname,
              src,
            }:
              pkgs.rocqPackages.mkRocqDerivation {
                inherit meta pname version;

                opam-name = pname;
                src = lib.rust.cargoRefinedRust {
                  inherit meta pname src version;

                  cargoArtifacts = null;
                  cargoExtraArgs = "";
                  cargoVendorDir = null;
                };

                buildInputs = [packages.stdlib extraProofs];
                useDune = true;
              };
        in
          {
            clippy = lib.rust.cargoClippy rust.toolchain.dev {
              inherit (packages.frontend.passthru) cargoArtifacts pname src;

              cargoClippyExtraArgs = "--all-targets --all-features --no-deps";
            };

            deny = lib.rust.cargoDeny {
              inherit (packages.frontend.passthru) pname src;
            };

            fmt = lib.rust.cargoFmt rust.toolchain.dev {
              inherit (packages.frontend.passthru) pname src;
            };

            machete = lib.rust.cargoMachete {
              inherit (packages.frontend.passthru) pname src;
            };
          }
          // lib.mapToAttrs id mkCaseStudies [
            {
              pname = "case-study-evenint";
              src = ./case_studies/evenint;
            }
            {
              pname = "case-study-minivec";
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
          ];

        devShells =
          {
            default = devShells."target-${lib.rust.hostPlatform}";
          }
          // (
            rust.mkDrvRustTargetToolchains (toolchain:
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
