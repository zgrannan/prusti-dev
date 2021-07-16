{}:

let
  rust-overlay = (import (builtins.fetchTarball "https://github.com/oxalica/rust-overlay/archive/master.tar.gz"));

  pkgs = import <nixpkgs> {
    # overlays = [ rust-overlay ];
  };
in
  with pkgs;

  mkShell {
    shellHook = ''export VIPER_HOME=/home/zgrannan/prusti-dev/viper_tools/backends'';
    buildInputs = [
      openssl pkg-config
      # (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain)
    ];
  }
