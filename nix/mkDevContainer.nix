pkgs: drvs: rustAnalyzer:

let
  rustAnalyzerExtension = pkgs.vscode-extensions.rust-lang.rust-analyzer.override {
    rust-analyzer = rustAnalyzer;
  };

  os-release = pkgs.writeTextFile {
    destination = "/etc/os-release";
    name = "os-release";
    text = "ID=nixos";
  };

  userContents = drvs ++ [
    pkgs.python3
    pkgs.rocqPackages.vsrocq-language-server
    pkgs.tokei
    pkgs.vscode-extensions.rocq-prover.vsrocq
    rustAnalyzerExtension
  ];
in
pkgs.dockerTools.buildLayeredImage {
  name = "refinedrust-devcontainer";
  tag = "latest";

  contents = [
    os-release
    pkgs.bash
    pkgs.busybox
    pkgs.patchelf
    pkgs.dockerTools.caCertificates
    pkgs.dockerTools.usrBinEnv
  ]
  ++ userContents;

  config = {
    Cmd = [ "/sbin/bash" ];
    Env = [
      "HOME=/root"
      "USER=root"
      "OCAMLPATH=/lib/ocaml/${pkgs.rocqPackages.rocq-core.ocamlPackages.ocaml.version}/site-lib"
      "ROCQPATH=/lib/coq/${pkgs.rocqPackages.rocq-core.rocq-version}/user-contrib"
      "VSCODE_SERVER_CUSTOM_GLIBC_LINKER=${pkgs.stdenv.cc.bintools.dynamicLinker}"
      "VSCODE_SERVER_CUSTOM_GLIBC_PATH=${pkgs.glibc.outPath}/lib:${pkgs.libgcc.lib.outPath}/lib"
      "VSCODE_SERVER_PATCHELF_PATH=${pkgs.patchelf.outPath}/bin/patchelf"
    ];
  };

  enableFakechroot = true;

  fakeRootCommands = ''
    echo "root:x:0:" > /etc/group
    echo "nobody:x:65534:" >> /etc/group

    echo "root:x:0:0:root user:/var/empty:/bin/sh" > /etc/passwd
    echo "nobody:x:65534:65534:nobody:/var/empty:/bin/sh" >> /etc/passwd

    mkdir -p /root/.vscode-server/extensions
    cp -r ${pkgs.vscode-extensions.rocq-prover.vsrocq}/share/vscode/extensions/* /root/.vscode-server/extensions/
    cp -r ${rustAnalyzerExtension}/share/vscode/extensions/* /root/.vscode-server/extensions/

    mkdir -p /root/.cargo
    mv /config.toml /root/.cargo/config.toml
  '';
}
