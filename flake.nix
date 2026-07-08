{
  description = "wowsdeob - World of Warships Python 2.7 script deobfuscator";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
    crane.url = "github:ipetkov/crane";
  };

  outputs = {
    self,
    nixpkgs,
    rust-overlay,
    flake-utils,
    crane,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      overlays = [(import rust-overlay)];
      pkgs = import nixpkgs {inherit system overlays;};

      rustToolchainToml = fromTOML (builtins.readFile ./rust-toolchain.toml);
      inherit (rustToolchainToml.toolchain) channel components;

      # minimal (rustc + cargo + rust-std) keeps the build lean; the components
      # from rust-toolchain.toml (rustfmt, clippy) are added for the dev shell.
      rustToolchain = pkgs.rust-bin.stable.${channel}.minimal.override {
        extensions = components;
      };

      craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;

      # wowsdeob is pure Rust (zip/flate2 via miniz_oxide, memmap, petgraph);
      # no system libraries, so commonArgs needs no build inputs.
      commonArgs = {
        src = craneLib.cleanCargoSource ./.;
        strictDeps = true;
      };

      cargoArtifacts = craneLib.buildDepsOnly commonArgs;

      wowsdeob = craneLib.buildPackage (commonArgs
        // {
          inherit cargoArtifacts;
          meta.mainProgram = "wowsdeob";
        });
    in {
      packages.default = wowsdeob;
      packages.wowsdeob = wowsdeob;

      apps.default = flake-utils.lib.mkApp {drv = wowsdeob;};

      devShells.default = craneLib.devShell {
        packages = [];
      };
    });
}
