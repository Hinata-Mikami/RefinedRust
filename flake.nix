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
          version = "2d5412f48adadeb69fb3115da4d83075c9ba15bf";
          sha256 = "sha256-GXo9G+bF4wIdMrkedj7/yQnf/4n75kOWmj26g3rjgbg";
        };

        iris = {
          version = "3e83a7affa51b91aa1eaab1fc0d8a68e5a38b221";
          sha256 = "sha256-wL95wD0sESzzU7dCZCPw9pMzfJgz06MV/mWbYWjs+k8=";
        };

        iris-contrib = {
          version = "4e3ace9604b7ec7a1826cd3563b05f1ef9be0dfd";
          sha256 = "sha256-+7MR4MGzHMNgio8GN4bEwnIpJO96MUzW2kbEedPf+Xk=";
        };

        lambda-rust = {
          version = "a13bc8df1c0d9824d6fe51f9572f6485c5ce4fab";
          sha256 = "sha256-d7gbHIDfS5KWeMIEpEFIaiGWm+h2ZsS+J17uC5x1OMk=";
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
