{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";

    crane.url = "github:ipetkov/crane";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    flake-utils,
    nixpkgs,
    ...
  } @ inputs:
    flake-utils.lib.eachDefaultSystem (system: let
      inherit (lib) pkgs;

      lib = nixpkgs.lib.extend (_: _: (import ./nix {
        inherit inputs system;
      }));

      name = "refinedrust";
      version = "0.1.0";

      meta = {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = lib.licenses.bsd3;
      };

      rocq = {
        stdpp = {
          version = "ad890e18391e7f0a3675c7f257519d9e3dbc36c1";
          sha256 = "sha256-utYUzGguteRcHWKjxumi4wRVlkqS0HEn9GE/tRY71VY=";
        };

        iris = {
          version = "b0482dbb04dc8a87fa719bf3317f2b0ad4f4b995";
          sha256 = "sha256-a/inYe08dVqAQUhlduNgPPAE1Bd0ENzz0Is5AcxRZHg=";
        };

        iris-contrib = {
          version = "809f20037565ace0f54903d9c560ead91a6ed538";
          sha256 = "sha256-q5tEhUFOqZcAicB+kytLpE70mif5sFvb8z8w8CW3qTM=";
        };

        lambda-rust = {
          version = "2d20dc5def11269b2c4ef17f43a3dddd54f3bb46";
          sha256 = "sha256-9uKI8hqOlMAeN10IlvgRIG+4gyZGQ9g7m6HQofHWwbA=";
        };
      };

      rust = let
        inherit (toolchainFile) channel components;
        toolchainFile = (lib.importTOML ./rr_frontend/rust-toolchain.toml).toolchain;
        devComponents = ["clippy" "rust-analyzer" "rust-src" "rustfmt"];
      in rec {
        toolchain = rec {
          inherit channel;

          build = lib.rust.mkToolchain channel components;
          dev = lib.rust.mkToolchain channel (components ++ devComponents);
        };

        envBuilder = lib.rust.overrideToolchain toolchain.build;
      };
    in rec {
      inherit lib;

      packages = {
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
                --set-default LD_LIBRARY_PATH ${rust.toolchain.build}/lib \
                --set-default DYLD_FALLBACK_LIBRARY_PATH ${rust.toolchain.build}/lib
            '';

            doNotRemoveReferencesToRustToolchain = true;
            passthru = {inherit cargoArtifacts pname src;};
          };

          default = let
            mkRefinedRust = toolchain:
              pkgs.symlinkJoin {
                inherit meta name;

                paths = let
                  fetchRocqDeps = drv: lib.lists.unique ([drv] ++ lib.flatten (map fetchRocqDeps drv.propagatedBuildInputs));
                in
                  [pkgs.gcc pkgs.gnupatch packages.frontend toolchain]
                  ++ ([pkgs.rocqPackages.rocq-core] ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs)
                  ++ (fetchRocqDeps packages.stdlib);

                nativeBuildInputs = [pkgs.makeWrapper];
                postBuild = ''
                  wrapProgram $out/bin/dune \
                    --set OCAMLPATH $out/lib/ocaml/${pkgs.ocaml.version}/site-lib \
                    --set ROCQPATH $out/lib/coq/${pkgs.rocqPackages.rocq-core.rocq-version}/user-contrib

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
            in mkRefinedRust rust.toolchain.build;
          stdlib = pkgs.rocqPackages.mkRocqDerivation {
            inherit meta version;

            pname = "stdlib";
            opam-name = "refinedrust-stdlib";
            src = ./stdlib;

            propagatedBuildInputs = [packages.theories];
            useDune = true;
          };
        };

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

                cargoRefinedRustArgs = {
                  toolchain = rust.toolchain.build;
                };
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
        // lib.mapToAttrs lib.id mkCaseStudies [
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
            pname = "tests";
            src = ./case_studies/tests;
          }
        ];

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend theories];
        packages = with pkgs; [cargo-deny cargo-machete gnumake gnupatch gnused rust.toolchain.dev];

        LD_LIBRARY_PATH = lib.makeLibraryPath [rust.toolchain.dev];
        DYLD_FALLBACK_LIBRARY_PATH = lib.makeLibraryPath [rust.toolchain.dev];
        LIBCLANG_PATH = lib.makeLibraryPath [pkgs.libclang.lib];
      };

      formatter = pkgs.alejandra;
    });
}
