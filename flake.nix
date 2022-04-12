{
  description = "Nix flake for Telomare";

  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  # See https://input-output-hk.github.io/haskell.nix/tutorials/getting-started-flakes.html
  inputs.haskellNix.url = "github:input-output-hk/haskell.nix";
  inputs.nixpkgs.follows = "haskellNix/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.hvm.url = "github:hhefesto/HVM";

  outputs = { self, nixpkgs, flake-utils, haskellNix, flake-compat, hvm }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let
      overlays = [ haskellNix.overlay

                   (final: prev: {
                     # This overlay adds our project to pkgs
                     jumper = final.stdenv.mkDerivation {
                       name = "telomareJumper";
                       src = ./cbits;
                       buildInputs = [ final.boehmgc ];
                     };
                     gc = final.boehmgc;

                     telomare = final.haskell-nix.cabalProject {
                       src = final.haskell-nix.cleanSourceHaskell {
                         src = ./.;
                         name = "telomare";
                       };

                       compiler-nix-name = "ghc8107";
                       # compiler-nix-name = "ghc922"; # TODO

                       shell.tools = {
                         cabal = {};
                         haskell-language-server = {};
                         ghcid = {};
                       };
                       # Non-Haskell shell tools go here
                       shell.buildInputs = with pkgs; [
                         # broken if provided by shell.tools
                         stylish-haskell
                         hlint
                         hvm.defaultPackage."x86_64-linux"
                       ];
                     };
                   })
                 ];
      pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };
      flake = pkgs.telomare.flake {};
    in flake // {
      # Built by `nix build .`
      defaultPackage = flake.packages."telomare:exe:telomare";
      checks = {
        build = self.defaultPackage.x86_64-linux;
        telomareTest0 = flake.packages."telomare:test:telomare-test";
        telomareTest1 = flake.packages."telomare:test:telomare-parser-test";
        telomareTest2 = flake.packages."telomare:test:telomare-serializer-test";
      };
    });
}
