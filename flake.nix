{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";

    crane.url = "github:ipetkov/crane";

    rust-targets = {
      url = "file+https://raw.githubusercontent.com/oxalica/rust-overlay/refs/heads/master/manifests/targets.nix";
      flake = false;
    };

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
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
      ocamlFlambda = _: prev: rec {
        # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
        # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.05/pkgs/applications/science/logic/rocq-core/default.nix#L15
        ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (final: prev: {
          ocaml = prev.ocaml.override {
            flambdaSupport = true;
          };

          # NOTE: Remove this when `dune` will handle `rocq` subcommands
          # See: https://github.com/ocaml/dune/issues/11572
          dune_3 = prev.dune_3.overrideAttrs (prev: {
            nativeBuildInputs = prev.nativeBuildInputs ++ [pkgs.makeWrapper];

            postFixup = let
              coqSubcommand = newCmd: oldCmd:
                pkgs.writeScriptBin oldCmd ''
                  #!/bin/sh
                  unset COQPATH
                  rocq ${newCmd} "$@"
                '';

              coqc = coqSubcommand "compile" "coqc";
              coqdep = coqSubcommand "dep" "coqdep";
              coqpp = coqSubcommand "pp-mlg" "coqpp";
            in ''
              wrapProgram $out/bin/dune \
                --prefix PATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
                --prefix OCAMLPATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
                --run "export COQPATH=\$(eval echo \$ROCQPATH)"
            '';
          });
        });

        rocqPackages = prev.rocqPackages.overrideScope (_: prev: {
          rocq-core = prev.rocq-core.override {
            customOCamlPackages = ocamlPackages;
          };
        });
      };

      overlays = [ocamlFlambda rust-overlay.overlays.default];
      pkgs = import nixpkgs {inherit overlays system;};

      name = "refinedrust";
      version = "0.1.0";

      meta = with pkgs.lib; {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = licenses.bsd3;
      };

      ocaml = {
        pkgs = pkgs.ocamlPackages;
        version = pkgs.ocaml.version;
      };

      rocq = {
        pkgs = pkgs.rocqPackages;
        toolchain = [rocq.pkgs.rocq-core] ++ rocq.pkgs.rocq-core.nativeBuildInputs;

        version = rocq.pkgs.rocq-core.rocq-version;

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
        craneLib = crane.mkLib pkgs;
        hostPlatform = pkgs.stdenv.hostPlatform.rust.rustcTarget;
        toolchain = rust.mkToolchain rust.hostPlatform;

        mkToolchain = target: let
          addRustSrc =
            attrsets.optionalAttrs (target != rust.hostPlatform) {extensions = ["rust-src"];};
        in rec {
          build = (pkgs.rust-bin.fromRustupToolchain inputsToolchain // {targets = [target];}).override addRustSrc;
          dev = build.override {extensions = inputsToolchain.components ++ devComponents;};
          envBuilder = rust.craneLib.overrideToolchain build;
        };

        mkTargetToolchains = drv:
          listToAttrs (map (target: {
              name = "target-" + target;
              value = drv (rust.mkToolchain target);
            })
            availableTargets);
      };
    in rec {
      packages =
        {
          theories = let
            mkDepRocqDerivation = pin: {
              pname,
              propagatedBuildInputs ? [rocq.pkgs.stdlib],
              owner ? "iris",
            }:
              rocq.pkgs.mkRocqDerivation {
                inherit pname propagatedBuildInputs owner;

                domain = "gitlab.mpi-sws.org";
                # NOTE: Remove `sed` line when Makefiles will be updated upstream
                preBuild = ''
                  sed -i -e 's/"$(COQBIN)coq_makefile"/"$(COQBIN)rocq" makefile/g' Makefile
                  patchShebangs coq-lint.sh
                '';

                release.${pin.version}.sha256 = "${pin.sha256}";
                version = pin.version;
              };

            # NOTE: Remove `coq-record-update` and `equations` when available in Nix's `RocqPackages`
            equations = rocq.pkgs.mkRocqDerivation {
              pname = "equations";
              owner = "mattam82";
              repo = "Coq-Equations";
              opam-name = "rocq-equations";

              propagatedBuildInputs = [rocq.pkgs.stdlib ocaml.pkgs.ppx_optcomp];

              mlPlugin = true;
              useDune = true;

              version = "2ce6d98dd03979369d739ac139db4da4f7eab352";
              release = {
                "2ce6d98dd03979369d739ac139db4da4f7eab352".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
              };
            };

            stdpp = mkDepRocqDerivation rocq.stdpp {
              pname = "stdpp";
            };

            iris = mkDepRocqDerivation rocq.iris {
              pname = "iris";

              propagatedBuildInputs = [stdpp];
            };

            iris-contrib = mkDepRocqDerivation rocq.iris-contrib {
              pname = "iris-contrib";

              propagatedBuildInputs = [iris];
            };

            lambda-rust = mkDepRocqDerivation rocq.lambda-rust {
              pname = "lambda-rust";

              propagatedBuildInputs = [iris];
            };
          in
            rocq.pkgs.mkRocqDerivation {
              inherit meta version;

              pname = name;
              opam-name = name;
              src = ./theories;

              propagatedBuildInputs = [equations iris-contrib lambda-rust];

              preBuild = "dune() { command dune $@ --display=short; }";
              useDune = true;
            };

          frontend = let
            src = ./rr_frontend;
            pname = "cargo-${name}";

            cargoArtifacts = rust.toolchain.envBuilder.buildDepsOnly {
              inherit meta pname src version;
            };
          in
            with pkgs;
              rust.toolchain.envBuilder.buildPackage rec {
                inherit cargoArtifacts meta pname src version;

                buildInputs = [pkgs.gnupatch];
                nativeBuildInputs = with pkgs;
                  [makeWrapper]
                  ++ lib.optionals stdenv.isDarwin [libiconv libzip];

                postFixup = with pkgs.lib.strings; ''
                  wrapProgram $out/bin/${pname} \
                    --set PATH "${makeBinPath buildInputs}" \
                '';

                doNotRemoveReferencesToRustToolchain = true;

                passthru = {inherit cargoArtifacts pname src;};
              };

          stdlib = rocq.pkgs.mkRocqDerivation {
            inherit meta version;

            pname = "refinedrust-stdlib";
            opam-name = "refinedrust-stdlib";
            src = ./stdlib;

            buildInputs = [packages.frontend rust.toolchain.build];
            propagatedBuildInputs = [packages.theories];

            preBuild = ''
              dune() { command dune $@ --display=short; }
              make generate_stdlib
            '';
            useDune = true;
          };

          default = packages."target-${rust.hostPlatform}";
        }
        // (
          rust.mkTargetToolchains (toolchain:
            pkgs.buildEnv {
              inherit meta;

              name = "cargo-${name}";
              paths = rocq.toolchain ++ [packages.frontend toolchain.build];

              pathsToLink = ["/bin"];
              nativeBuildInputs = [pkgs.makeWrapper];

              postBuild = let
                fetchRocqDeps = with pkgs.lib;
                  drv: lists.unique [drv] ++ flatten (map fetchRocqDeps drv.propagatedBuildInputs);
              in
                with pkgs.lib.strings; ''
                  wrapProgram $out/bin/dune \
                    --set OCAMLPATH "${makeSearchPath "lib/ocaml/${ocaml.version}/site-lib" ([rocq.pkgs.rocq-core] ++ (fetchRocqDeps packages.stdlib))}" \
                    --set ROCQPATH "${makeSearchPath "lib/coq/${rocq.version}/user-contrib" (fetchRocqDeps packages.stdlib)}"

                  wrapProgram $out/bin/cargo-refinedrust \
                    --set LD_LIBRARY_PATH "${pkgs.lib.makeLibraryPath [toolchain.build]}" \
                    --set DYLD_FALLBACK_LIBRARY_PATH "${pkgs.lib.makeLibraryPath [toolchain.build]}" \
                    --set RR_NIX_STDLIB "${packages.stdlib}"/share/refinedrust-stdlib/
                '';

              passthru = {inherit toolchain;};
            })
        );

      devShells =
        {
          default = devShells."target-${rust.hostPlatform}";
        }
        // (
          rust.mkTargetToolchains (toolchain:
            pkgs.mkShell {
              inputsFrom = with packages; [frontend theories];
              packages = with pkgs; [cargo-deny cargo-machete gnumake gnupatch gnused toolchain.dev];

              LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [toolchain.dev];
              DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [toolchain.dev];
              LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.libclang.lib];
            })
        );

      formatter = pkgs.alejandra;
    });
}
