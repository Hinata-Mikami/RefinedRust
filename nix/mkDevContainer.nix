pkgs: refinedrust:

let
  os-release = pkgs.writeTextFile {
    destination = "/etc/os-release";
    name = "os-release";
    text = "ID=nixos";
  };
in
pkgs.dockerTools.buildLayeredImage {
  name = "refinedrust-devcontainer";
  contents = [
    refinedrust
    os-release
  ]
  ++ (with pkgs; [
    bash
    busybox
    gnumake
    patchelf
  ])
  ++ (with pkgs.dockerTools; [
    caCertificates
    usrBinEnv
  ])
  ++ (with pkgs.rocqPackages; [
    vsrocq-language-server
  ])
  ++ (with pkgs.vscode-extensions; [
    rocq-prover.vsrocq
  ]);

  config = {
    Cmd = [ "/bin/sh" ];
    Env = [
      "HOME=/root"
      "USER=root"
      "VSCODE_SERVER_CUSTOM_GLIBC_LINKER=${pkgs.glibc.outPath}/lib/ld-linux-x86-64.so.2"
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
  '';
}
