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
    in rec {
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

          default = packages."target-${rust.hostPlatform}";
        }
        // (
          rust.mkTargetToolchains (toolchain:
            pkgs.symlinkJoin {
              inherit meta name;

              paths = [pkgs.rocqPackages.rocq-core packages.frontend toolchain.build pkgs.gnupatch] ++ pkgs.rocqPackages.rocq-core.nativeBuildInputs;

              nativeBuildInputs = [pkgs.makeWrapper];

              postBuild = let
                fetchRocqDeps = with pkgs.lib;
                  drv: lists.unique [drv] ++ flatten (map fetchRocqDeps drv.propagatedBuildInputs);
              in
                with pkgs.lib.strings; ''
                  wrapProgram $out/bin/dune \
                    --set OCAMLPATH "${makeSearchPath "lib/ocaml/${ocaml.version}/site-lib" ([pkgs.rocqPackages.rocq-core] ++ (fetchRocqDeps packages.stdlib))}" \
                    --set ROCQPATH "${makeSearchPath "lib/coq/${rocq.version}/user-contrib" (fetchRocqDeps packages.stdlib)}"

                  wrapProgram $out/bin/cargo-${name} \
                    --set LD_LIBRARY_PATH "${pkgs.lib.makeLibraryPath [toolchain.build]}" \
                    --set DYLD_FALLBACK_LIBRARY_PATH "${pkgs.lib.makeLibraryPath [toolchain.build]}" \
                    --set PATH "$out/bin" \
                    --set RR_NIX_STDLIB "${packages.stdlib}"/share/refinedrust-stdlib/
                '';

              passthru = {inherit toolchain;};
            })
        );

      checks = {
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

        evenInt = pkgs.rocqPackages.mkRocqDerivation rec {
          inherit meta version;

          pname = "evenint";
          opam-name = "evenint";

          src = rust.lib.cargoRefinedRust {
            inherit (packages.frontend.passthru) cargoArtifacts;
            inherit meta pname version;

            src = ./case_studies/evenint;

            cargoExtraArgs = "";
            cargoVendorDir = null;
          };

          propagatedBuildInputs = [packages.stdlib];
          useDune = true;
        };
      };

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
