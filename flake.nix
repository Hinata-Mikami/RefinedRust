{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";

    crane.url = "github:ipetkov/crane";

    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    crane,
    fenix,
    flake-utils,
    nixpkgs,
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

            postInstall = let
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
      overlays = [fenix.overlays.default ocamlFlambda];
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
          version = "567f831ef317c62ecc4413d018370b3dcbdf4c39";
          sha256 = "sha256-jZXhDPVRtkDd+1FXCYqU0r/Mq3JDWOPL1Uk9wJjgrqI=";
        };

        iris = {
          version = "710391513c6d74904ae48b17ae681ca1c20fb98e";
          sha256 = "sha256-EdRLHmejsDX6ggWH0ZLka4/zRcuuaxcvfiScQaoh6/I=";
        };

        iris-contrib = {
          version = "53c49f2fcae1a4a9c3bfa547b7de10911a72a8c3";
          sha256 = "sha256-D1NoltpSDBXEDW9QiVl/EYubxkEyByIbUst45qCL0Eg=";
        };

        lambda-rust = {
          version = "0f4ebd6d9a3a6cf2e0a18dfe794134481b7b4bfc";
          sha256 = "sha256-8ncIi9HyD1TedNkHFhI8wKvrvyiJfdZv/mbS3zOGvvg=";
        };
      };

      rust = {
        toolchain = pkgs.fenix.fromToolchainFile {
          file = ./rr_frontend/rust-toolchain.toml;
          sha256 = "sha256-AXPEAqDScBO5JmUk086vVIZqHxkWcwpT7R5SUo6DSCY=";
        };

        env = (crane.mkLib pkgs).overrideToolchain rust.toolchain;
        lib = "${rust.toolchain}/lib/rustlib/$(rustc -Vv | grep '^host:' | cut -d' ' -f2)/lib";
        src = "${rust.toolchain}/lib/rustlib/rustc-src/rust/compiler";
      };
    in rec {
      packages = let
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
      in {
        theories = let
          # NOTE: Remove `coq-record-update` and `equations` when available in Nix's `RocqPackages`
          coq-record-update = rocq.pkgs.mkRocqDerivation {
            pname = "coq-record-update";
            owner = "tchajed";

            version = "0247521c76dd3f54a7ef1a8ba531ef4b81c13570";
            release = {
              "0247521c76dd3f54a7ef1a8ba531ef4b81c13570".sha256 = "sha256-AhEcugUiVIsgbq884Lur/bQIuGw8prk+3AlNkP1omcw=";
            };

            buildFlags = ["NO_TEST=1"];
            preBuild = ''
              sed -i -e 's/"$(COQBIN)coq_makefile"/"$(COQBIN)rocq" makefile/g' Makefile
            '';
          };

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

            propagatedBuildInputs = [coq-record-update equations iris-contrib lambda-rust];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };

        frontend = let
          src = ./rr_frontend;
          pname = "cargo-${name}";

          cargoArtifacts = rust.env.buildDepsOnly {
            inherit meta pname src version;
          };
        in
          rust.env.buildPackage rec {
            inherit cargoArtifacts meta pname src version;

            buildInputs = [rust.toolchain pkgs.gnupatch];
            nativeBuildInputs = with pkgs;
              [makeWrapper]
              ++ lib.optionals stdenv.isDarwin [libiconv libzip];

            doNotRemoveReferencesToRustToolchain = true;

            postInstall = with pkgs.lib.strings; ''
              wrapProgram $out/bin/refinedrust-rustc \
                --set LD_LIBRARY_PATH "${rust.lib}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${rust.lib}"

              wrapProgram $out/bin/${pname} \
                --set PATH "${makeSearchPath "bin" buildInputs}" \
                --set LD_LIBRARY_PATH "${rust.lib}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${rust.lib}"
            '';

            doCheck = false;
          };

        stdlib = rocq.pkgs.mkRocqDerivation {
          inherit meta version;

          pname = "refinedrust-stdlib";
          opam-name = "refinedrust-stdlib";
          src = ./stdlib;

          buildInputs = [packages.frontend rust.toolchain];
          propagatedBuildInputs = [packages.theories];

          preBuild = ''
            dune() { command dune $@ --display=short; }
            make generate_stdlib
          '';
          useDune = true;
        };

        default = pkgs.buildEnv {
          inherit meta;

          name = "cargo-${name}";
          paths = rocq.toolchain ++ [packages.frontend rust.toolchain];

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
                --set RR_NIX_STDLIB "${packages.stdlib}"/share/refinedrust-stdlib/
            '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend theories];
        packages = with pkgs; [cargo-deny cargo-machete gnumake gnupatch gnused];

        shellHook = ''
          export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH}:${rust.lib}
          export DYLD_FALLBACK_LIBRARY_PATH=''${DYLD_FALLBACK_LIBRARY_PATH}:${rust.lib}
          export RUST_SRC_PATH=${rust.src}/rustc_driver/Cargo.toml
        '';
      };

      formatter = pkgs.alejandra;
    });
}
