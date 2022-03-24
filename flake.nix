{
  description = "Nix flake for Telomare";

  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  # See https://input-output-hk.github.io/haskell.nix/tutorials/getting-started-flakes.html
  inputs.haskellNix.url = "github:input-output-hk/haskell.nix";
  inputs.nixpkgs.follows = "haskellNix/nixpkgs-unstable";
  # inputs.nixpkgs.follows = "haskellNix/nixpkgs-2105";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils, haskellNix, flake-compat }:
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
          # llvm-config = final.llvm_9;
          # alex = final.haskellPackages.alex;

          telomare = final.haskell-nix.cabalProject {
            # If these null parameters are absent, you get a RestrictedPathError error
            # from trying to do readIfExists on cabal.project file
            # cabalProjectFreeze = null;
            # cabalProject = null;
            # cabalProjectLocal = null;
            # index-state = "2022-03-21T00:00:00Z";
            src = final.haskell-nix.cleanSourceHaskell {
              src = ./.;
              name = "telomare";
            };

            compiler-nix-name = "ghc8107";
            # compiler-nix-name = "ghc884";
            # compiler-nix-name = "ghc922";

            shell.tools = {
                cabal = {};
                # hlint = {};
                haskell-language-server = {};
                ghcid = {};
                # stylish-haskell = {
                #   # index-state = "2020-10-08T00:00:00Z";
                # };
            };
            # Non-Haskell shell tools go here
            shell.buildInputs = with pkgs; [
                # broken if provided by shell.tools
                stylish-haskell
            ];
            # modules = [
            #   { reinstallableLibGhc = true; }
            # ];

            # pkg-def-extras = with final.haskell.lib; [];
             #   (hackage: {
             #     llvm-hs = hackage.llvm-hs."9.0.1".revisions.default;
             #     llvm-hs-pure = hackage.llvm-hs-pure."9.0.0".revisions.default;
             #   })
             # ];
          };
        })
      ];
      # pkgs = import nixpkgs { inherit system overlays; };
      pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };
      flake = pkgs.telomare.flake {};
      something = builtins.trace overlays overlays;
    in flake // {
      # Built by `nix build .`
      defaultPackage = flake.packages."telomare:exe:telomare";
      checks = {
        build = self.defaultPackage.x86_64-linux;
        telomareTest0 = flake.packages."telomare:test:telomare-test";
        telomareTest1 = flake.packages."telomare:test:telomare-parser-test";
        telomareTest2 = flake.packages."telomare:test:telomare-serializer-test";
      };
      # This is used by `nix develop .` to open a shell for use with
      # `cabal`, `hlint` and `haskell-language-server`
      # devShell = pkgs.telomare.shellFor {
      #   tools = {
      #     cabal = "latest";
      #     hlint = "latest";
      #     haskell-language-server = "latest";
      #     ghcid = "latest";
      #     stylish-haskell = "latest";
      #   };
      # };
    });
}
