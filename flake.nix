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
          version = "9b19c60ce8fb8ccc518b5ecdbf025642afab7835";
          sha256 = "sha256-BJ3nmS//EQFaU4kaJsUTZ9MO5zw3V3aoCPB62I0h/OI=";
        };

        iris = {
          version = "8a8f05fb7de603d25df5797d1ba5a0efb2cbc658";
          sha256 = "sha256-Ypffk0cnhKRODRQylsP3/kyRQ2dSMOJ1sCkA/v89z34=";
        };

        lambda-rust = {
          version = "74bdf4e8a67147232f0a80ab6f648c20503a76bb";
          sha256 = "sha256-cq5eroG13wnfbFGGLuqCm+9425ZmPaboj7CZaPBx35g=";
        };
      };

      rust = {
        toolchain = pkgs.fenix.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-0NR5RJ4nNCMl9ZQDA6eGAyrDWS8fB28xIIS1QGLlOxw=";
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
