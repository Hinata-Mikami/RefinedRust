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
          version = "2301f95c0bf0c336b64d9f0d6cb26668ce35fd8c";
          sha256 = "sha256-xz0lYc+G0UGk9uSJNFvn04EylmloQE1uaQrmsVCq4Xo=";
        };

        iris = {
          version = "aa39151cf17dbfd53649a4466a6420c3dbb02a96";
          sha256 = "sha256-3y4j0Pkg2jUxTJZcLoZTsnL1E2WCRq+f6aaJFD7TvSU=";
        };

        iris-contrib = {
          version = "35ebb0772e832eb535b20c6195375ec593c9081b";
          sha256 = "sha256-v/AS2WPpEVCTsY18QwFRPg+qhiGxkIHgy5qZK4vyZrk=";
        };

        lambda-rust = {
          version = "804c0168f773731b669110872bd72e6cce05e755";
          sha256 = "sha256-lhyYAO4FybaqxbvyLUNkNTBqexLMkhPZ9fjX5wSck/g=";
        };

        smtcoq = {
          version = "3df6204826a06f5025bc7408ab77855680c50367";
          sha256 = "sha256-b1Me3obsZjPdBqTg6Si5Wz90eEIIrtI8O5Yxio9xPmI=";
        };

        sniper = {
          version = "c1ba4e90eea5af636de15c53a3e0a8ab29442a29";
          sha256 = "sha256-5vVbVU6qMHJd/mkS05VxKF204S3EqeVRmEUC/rYvjcQ=";
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

      dependencies = rec {
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

        smtcoq = pkgs.rocqPackages.mkRocqDerivation rec {
          inherit (rocq.smtcoq) version;

          pname = "smtcoq";
          owner = "smtcoq";
          repo = "smtcoq";

          mlPlugin = true;
          propagatedBuildInputs = with pkgs; [ocamlPackages.num rocqPackages.stdlib rocqPackages.trakt verit];

          release.${version}.sha256 = "${rocq.smtcoq.sha256}";
        };

        sniper = pkgs.rocqPackages.mkRocqDerivation rec {
          inherit (rocq.sniper) version;

          pname = "sniper";
          owner = "smtcoq";
          repo = "sniper";

          mlPlugin = true;
          propagatedBuildInputs = [pkgs.rocqPackages.metarocq-template smtcoq];

          release.${version}.sha256 = "${rocq.sniper.sha256}";
        };
      };
    in rec {
      inherit lib;

      packages = let
        mkStdlib = {
          pname,
          opam-name ? pname,
          ...
        } @ origArgs: let
          args = builtins.removeAttrs origArgs ["pname" "opam-name"];
        in
          lib.rocq.mkRefinedRust ({
              inherit meta version;

              inherit pname opam-name;

              withStdlib = false;
              generateFiles = false;
              useDune = true;
              propagatedBuildInputs = [packages.refinedrust-smtcoq];

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
            // args);

        stdlibLeafPkgs =
          lib.attrsets.attrValues
          (lib.filterAttrs (name: _: lib.strings.hasPrefix "stdlib-" name && name != "stdlib-stdlib") packages);
      in
        {
          refinedrust = pkgs.rocqPackages.mkRocqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;
            src = ./theories;

            propagatedBuildInputs = [pkgs.rocqPackages.equations dependencies.iris-contrib dependencies.lambda-rust];
            useDune = true;
          };

          refinedrust-smtcoq = pkgs.rocqPackages.mkRocqDerivation {
            inherit meta version;

            pname = name + "-smtcoq";
            opam-name = name + "-smtcoq";
            src = ./theories;

            propagatedBuildInputs = [packages.refinedrust dependencies.sniper];
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
          in
            mkRefinedRust rust.toolchain.build;
          # Expose the checked-in `stdlib/stdlib` package as the public stdlib
          # entry point. This matches the RefinedRust-level structure, where
          # `stdlib` is the logical top-level library, while the frontend finds
          # leaf stdlib libraries through the propagated stdlib load paths.
          stdlib = packages.stdlib-stdlib;
        }
        // lib.mapToAttrs lib.id mkStdlib [
          {
            pname = "stdlib-alloc";
            src = ./stdlib/alloc;
            libDeps = with packages; [stdlib-ptr stdlib-result stdlib-clone stdlib-mem stdlib-closures];
          }
          {
            pname = "stdlib-arithops";
            src = ./stdlib/arithops;
          }
          {
            pname = "stdlib-boxed";
            src = ./stdlib/boxed;
            libDeps = with packages; [stdlib-alloc stdlib-option stdlib-mem stdlib-ptr stdlib-rr_internal stdlib-ptr-advanced];
          }
          {
            pname = "stdlib-btreemap";
            src = ./stdlib/btreemap;
            libDeps = with packages; [stdlib-alloc stdlib-option stdlib-clone stdlib-cmp];
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
          }
          {
            pname = "stdlib-controlflow";
            src = ./stdlib/controlflow;
            libDeps = with packages; [stdlib-option stdlib-result];
          }
          {
            pname = "stdlib-iterator";
            src = ./stdlib/iterator;
            libDeps = with packages; [stdlib-clone stdlib-closures stdlib-cmp stdlib-option stdlib-range stdlib-result stdlib-controlflow];
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
          }
          {
            pname = "stdlib-option";
            src = ./stdlib/option;
            libDeps = with packages; [stdlib-closures stdlib-clone stdlib-result];
          }
          {
            pname = "stdlib-ptr";
            src = ./stdlib/ptr;
            libDeps = with packages; [stdlib-mem stdlib-clone stdlib-num stdlib-option];
          }
          {
            pname = "stdlib-ptr-advanced";
            src = ./stdlib/ptr_advanced;
            libDeps = with packages; [stdlib-mem stdlib-ptr stdlib-option stdlib-clone];
          }
          {
            pname = "stdlib-result";
            src = ./stdlib/result;
            libDeps = with packages; [stdlib-clone stdlib-closures];
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
            pname = "stdlib-spin";
            src = ./stdlib/spin;
            libDeps = with packages; [stdlib-option stdlib-closures stdlib-arithops];
          }
          {
            pname = "stdlib-vec";
            src = ./stdlib/vec;
            libDeps = with packages; [stdlib-alloc stdlib-iterator stdlib-option stdlib-rr_internal stdlib-closures stdlib-index stdlib-cmp stdlib-ptr-advanced stdlib-clone stdlib-controlflow];
          }
          {
            pname = "stdlib-stdlib";
            opam-name = "refinedrust-stdlib";
            src = ./stdlib/stdlib;
            libDeps = stdlibLeafPkgs;
          }
        ];

      checks = let
        mkCaseStudies = let
          extraProofs = pkgs.rocqPackages.mkRocqDerivation rec {
            inherit meta version;

            pname = "extra-proofs";
            opam-name = "extra-proofs";

            src = ./case_studies/extra_proofs;

            buildInputs = [packages.refinedrust-smtcoq];
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
        ];

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend refinedrust];
        packages = with pkgs; [cargo-deny cargo-machete gnumake rust.toolchain.dev dependencies.sniper];

        LD_LIBRARY_PATH = lib.makeLibraryPath [rust.toolchain.dev];
        DYLD_FALLBACK_LIBRARY_PATH = lib.makeLibraryPath [rust.toolchain.dev];
        LIBCLANG_PATH = lib.makeLibraryPath [pkgs.libclang.lib];
      };

      formatter = pkgs.alejandra;
    });
}
