{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.11";
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
        ocamlPackages = prev.ocamlPackages.overrideScope (_: prev: {
          ocaml = prev.ocaml.override {
            flambdaSupport = true;
          };
        });
        coqPackages = prev.coqPackages_8_20.overrideScope (_: prev: {
          coq = prev.coq.override {
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

      coq = {
        pkgs = pkgs.coqPackages;
        toolchain = [coq.pkgs.coq] ++ coq.pkgs.coq.nativeBuildInputs;
        version = coq.pkgs.coq.coq-version;

        stdpp = {
          version = "567f831ef317c62ecc4413d018370b3dcbdf4c39";
          sha256 = "sha256-jZXhDPVRtkDd+1FXCYqU0r/Mq3JDWOPL1Uk9wJjgrqI=";
        };

        iris = {
          version = "710391513c6d74904ae48b17ae681ca1c20fb98e";
          sha256 = "sha256-EdRLHmejsDX6ggWH0ZLka4/zRcuuaxcvfiScQaoh6/I=";
        };

        lambda-rust = {
          version = "0f4ebd6d9a3a6cf2e0a18dfe794134481b7b4bfc";
          sha256 = "sha256-8ncIi9HyD1TedNkHFhI8wKvrvyiJfdZv/mbS3zOGvvg=";
        };
      };

      rust = {
        toolchain = pkgs.fenix.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-GaU9WDiYBYSzYrUH8W+LODUvq1/epehgCmoX2YfnkiM=";
        };

        env = (crane.mkLib pkgs).overrideToolchain rust.toolchain;
        lib = "${rust.toolchain}/lib/rustlib/$(rustc -Vv | grep '^host:' | cut -d' ' -f2)/lib";
        src = "${rust.toolchain}/lib/rustlib/rustc-src/rust/compiler";
      };
    in rec {
      packages = let
        fetchCoqDeps = with pkgs.lib;
          drv: [drv] ++ flatten (map fetchCoqDeps drv.propagatedBuildInputs);

        mkDepCoqDerivation = pin: {
          pname,
          propagatedBuildInputs ? [],
          owner ? "iris",
        }:
          coq.pkgs.mkCoqDerivation {
            inherit pname propagatedBuildInputs owner;

            domain = "gitlab.mpi-sws.org";
            preBuild = "patchShebangs coq-lint.sh";

            release.${pin.version}.sha256 = "${pin.sha256}";
            version = pin.version;
          };
      in {
        theories = let
          stdpp = mkDepCoqDerivation coq.stdpp {
            pname = "stdpp";
          };

          iris = mkDepCoqDerivation coq.iris {
            pname = "iris";

            propagatedBuildInputs = [stdpp];
          };

          lambda-rust = mkDepCoqDerivation coq.lambda-rust {
            pname = "lambda-rust";

            propagatedBuildInputs = [iris];
          };
        in
          coq.pkgs.mkCoqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;

            src = ./theories;

            propagatedBuildInputs = with coq.pkgs; [coq-record-update equations lambda-rust];

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
              ++ lib.optionals stdenv.isDarwin [libzip libiconv];

            doNotRemoveReferencesToRustToolchain = true;

            postInstall = with pkgs.lib.strings; ''
              wrapProgram $out/bin/refinedrust-rustc \
                --set LD_LIBRARY_PATH "${rust.lib}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${rust.lib}"

              wrapProgram $out/bin/${pname} \
                --set PATH "${makeSearchPath "bin" buildInputs}"
            '';

            doCheck = false;
          };

        stdlib = coq.pkgs.mkCoqDerivation {
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
          paths = coq.toolchain ++ [packages.frontend rust.toolchain];

          pathsToLink = ["/bin"];
          nativeBuildInputs = [pkgs.makeWrapper];
          postBuild = with pkgs.lib.strings; ''
            wrapProgram $out/bin/dune \
              --set COQPATH "${makeSearchPath "lib/coq/${coq.version}/user-contrib" (fetchCoqDeps packages.stdlib)}"
          '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend theories];

        packages = with pkgs; [cargo-machete gnumake gnupatch gnused];

        shellHook = ''
          export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH}:${rust.lib}
          export DYLD_FALLBACK_LIBRARY_PATH=''${DYLD_FALLBACK_LIBRARY_PATH}:${rust.lib}
          export RUST_SRC_PATH=${rust.src}/rustc_driver/Cargo.toml
        '';
      };

      formatter = pkgs.alejandra;
    });
}
