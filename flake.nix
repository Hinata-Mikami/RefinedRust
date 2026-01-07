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

        mkToolchain = target: {
          build = lib.rust.mkToolchain channel components target;
          dev = lib.rust.mkToolchain channel (components ++ devComponents) target;
        };
      in rec {
        toolchain = mkToolchain lib.rust.hostPlatform;
        envBuilder = lib.rust.overrideToolchain toolchain.build;

        mkDrvRustTargetToolchains = drv:
          lib.mapToAttrs (target: "target-" + target) (target: drv (mkToolchain target))
          (map (pname: {inherit pname;}) (pkgs.lib.attrsets.attrValues (import rust-targets.outPath)));
      };
    in
      with pkgs.lib; rec {
        inherit lib;

        packages = let
          stdlibPkgs = with pkgs.lib; attrsets.attrValues (filterAttrs (name: _: strings.hasPrefix "stdlib-" name) packages);

          mkStdlib = {
            pname,
            opam-name ? pname,
            rocqTheoriesArgs ? {},
            withTheories ? false,
            ...
          } @ origArgs: let
            args = builtins.removeAttrs origArgs ["rocqTheoriesArgs"];
          in
            lib.rocq.mkRefinedRust ({
                inherit meta version;

                propagatedBuildInputs = [packages.theories];

                cargoArtifacts = null;
                withStdlib = false;

                cargoRefinedRustArgs = {
                  preBuild = ''
                    sed -i -e 's/rr::package("refinedrust-stdlib")/rr::package("${opam-name}")/g' ./src/lib.rs
                  '';
                };
              }
              // (
                if withTheories
                then {
                  rocqTheoriesArgs =
                    {
                      preBuild = ''
                        find . -name "dune" -exec sed -i -e '3s|.*|  (package ${opam-name}-theories)|g' {} \;
                        cat << EOF > dune-project
                        (lang dune 3.8)
                        (using coq 0.8)
                        (name ${opam-name}-theories)
                        (package (name ${opam-name}-theories))
                        EOF
                      '';
                    }
                    // rocqTheoriesArgs;
                }
                else rocqTheoriesArgs
              )
              // args);
        in
          {
            default = packages."target-${lib.rust.hostPlatform}";

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
                [makeWrapper]
                ++ (lib.optionals stdenv.isDarwin [libiconv libzip]);

              postInstall = ''
                wrapProgram $out/bin/${pname} \
                  --set LD_LIBRARY_PATH ${rust.toolchain.dev}/lib \
                  --set DYLD_FALLBACK_LIBRARY_PATH ${rust.toolchain.dev}/lib
              '';

              doNotRemoveReferencesToRustToolchain = true;
              passthru = {inherit cargoArtifacts pname src;};
            };
          }
          // lib.mapToAttrs id mkStdlib [
            {
              pname = "stdlib-alloc";
              src = ./stdlib/alloc;
              libDeps = with packages; [stdlib-ptr stdlib-result stdlib-clone];
              withTheories = true;
            }
            {
              pname = "stdlib-arithops";
              src = ./stdlib/arithops;
            }
            {
              pname = "stdlib-boxed";
              src = ./stdlib/boxed;
              libDeps = with packages; [stdlib-alloc stdlib-option stdlib-rr_internal];
              withTheories = true;
            }
            {
              pname = "stdlib-btreemap";
              src = ./stdlib/btreemap;
              libDeps = with packages; [stdlib-alloc stdlib-option];
            }
            {
              pname = "stdlib-clone";
              src = ./stdlib/clone;
              libDeps = with packages; [stdlib-sized];
            }
            {
              pname = "stdlib-closures";
              src = ./stdlib/closures;
            }
            {
              pname = "stdlib-cmp";
              src = ./stdlib/cmp;
              libDeps = with packages; [stdlib-closures stdlib-option];
              withTheories = true;
            }
            {
              pname = "stdlib-controlflow";
              src = ./stdlib/controlflow;
              libDeps = with packages; [stdlib-option stdlib-result];
            }
            {
              pname = "stdlib-iterator";
              src = ./stdlib/iterator;
              libDeps = with packages; [stdlib-clone stdlib-closures stdlib-cmp stdlib-option stdlib-range];
              withTheories = true;
            }
            {
              pname = "stdlib-sized";
              src = ./stdlib/sized;
            }
            {
              pname = "stdlib-index";
              src = ./stdlib/index;
              libDeps = with packages; [stdlib-sized];
            }
            {
              pname = "stdlib-mem";
              src = ./stdlib/mem;
              withTheories = true;
            }
            {
              pname = "stdlib-option";
              src = ./stdlib/option;
              libDeps = with packages; [stdlib-closures stdlib-clone stdlib-ptr stdlib-result];
            }
            {
              pname = "stdlib-ptr";
              src = ./stdlib/ptr;
              libDeps = with packages; [stdlib-mem];
              withTheories = true;
            }
            {
              pname = "stdlib-sized";
              src = ./stdlib/sized;
            }
            {
              pname = "stdlib-result";
              src = ./stdlib/result;
              libDeps = with packages; [stdlib-clone];
              withTheories = true;
            }
            {
              pname = "stdlib-range";
              src = ./stdlib/range;
              libDeps = with packages; [stdlib-cmp stdlib-option];
            }
            {
              pname = "stdlib-rr_internal";
              src = ./stdlib/rr_internal;
              libDeps = with packages; [stdlib-alloc stdlib-ptr];
              withTheories = true;
            }
            {
              pname = "stdlib-rwlock";
              src = ./stdlib/rwlock;
              withStdlib = false;
            }
            {
              pname = "stdlib-spin";
              src = ./stdlib/spin;
              libDeps = with packages; [stdlib-option];
              withTheories = true;

              rocqTheoriesArgs = {
                src = ./stdlib/spin/theories/once;
              };
            }
            {
              pname = "stdlib-vec";
              src = ./stdlib/vec;
              libDeps = with packages; [stdlib-alloc stdlib-iterator stdlib-option stdlib-rr_internal stdlib-closures stdlib-index stdlib-cmp];
            }
            {
              pname = "stdlib";
              opam-name = "refinedrust-stdlib";
              src = ./stdlib/stdlib;
              libDeps = stdlibPkgs;
            }
          ]
          // rust.mkDrvRustTargetToolchains (toolchain:
            pkgs.symlinkJoin {
              inherit meta name;

              paths = let
                fetchRocqDeps = with pkgs.lib;
                  drv: lists.unique ([drv] ++ flatten (map fetchRocqDeps drv.propagatedBuildInputs));
              in
                [pkgs.gcc pkgs.gnupatch packages.frontend toolchain.build]
                ++ ([pkgs.rocqPackages.rocq-core] ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs)
                ++ (fetchRocqDeps packages.stdlib);

              nativeBuildInputs = [pkgs.makeWrapper];
              postBuild = ''
                wrapProgram $out/bin/dune \
                  --set OCAMLPATH $out/lib/ocaml/${pkgs.ocaml.version}/site-lib \
                  --set ROCQPATH $out/lib/coq/${pkgs.rocqPackages.rocq-core.rocq-version}/user-contrib

                wrapProgram $out/bin/cargo-${name} \
                  --set PATH "$out/bin" \
                  --set RR_NIX_STDLIB $out/share/stdlib
              '';

              passthru = {inherit toolchain;};
            });

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
            args:
              lib.rocq.mkRefinedRust ({
                  inherit meta version;

                  propagatedBuildInputs = [extraProofs];

                  cargoArtifacts = null;
                  cargoExtraArgs = "";
                  cargoVendorDir = null;
                }
                // args);
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

            workspace-unused = lib.rust.cargoWorkspaceUnused rust.toolchain.dev {
              inherit (packages.frontend.passthru) pname src;
            };
          }
          // lib.mapToAttrs id mkCaseStudies [
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
          ];

        devShells =
          {
            default = devShells."target-${lib.rust.hostPlatform}";
          }
          // rust.mkDrvRustTargetToolchains (toolchain:
            pkgs.mkShell {
              inputsFrom = with packages; [frontend theories];
              packages = with pkgs; [cargo-deny cargo-machete gnumake gnupatch gnused toolchain.dev];

              LD_LIBRARY_PATH = makeLibraryPath [toolchain.dev];
              DYLD_FALLBACK_LIBRARY_PATH = makeLibraryPath [toolchain.dev];
              LIBCLANG_PATH = makeLibraryPath [pkgs.libclang.lib];
            });

        formatter = pkgs.alejandra;
      });
}
