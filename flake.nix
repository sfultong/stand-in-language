{
  description = "Nix flake for Telomare";

  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  inputs.haskellNix.url = "github:input-output-hk/haskell.nix";
  inputs.nixpkgs.follows = "haskellNix/nixpkgs-unstable";
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
          llvm-config = final.llvm_9;
          alex = final.haskellPackages.alex;

          telomare = final.haskell-nix.cabalProject {
            # If these null parameters are absent, you get a RestrictedPathError error
            # from trying to do readIfExists on cabal.project file
            cabalProjectFreeze = null;
            cabalProject = null;
            cabalProjectLocal = null;

            src = final.haskell-nix.cleanSourceHaskell {
              src = ./.;
              name = "telomare";
            };
            compiler-nix-name = "ghc884";
            pkg-def-extras = with final.haskell.lib; [
               (hackage: {
                 llvm-hs = hackage.llvm-hs."9.0.1".revisions.default;
                 llvm-hs-pure = hackage.llvm-hs-pure."9.0.0".revisions.default;
               })
             ];
            modules = [
              { reinstallableLibGhc = true; }
            ];
          };
        })
      ];
      pkgs = import nixpkgs { inherit system overlays; };
      flake = pkgs.telomare.flake {};
      flake1 = flake // { packages = flake.packages //
        {
          # This script is ran by Github Actions to do Haddock CI.
          # TODO: refactor to not use nix-shell.
          haddockScript = pkgs.writeShellScriptBin "updateHaddockScript" ''
            nix-shell --run "cabal haddock --haddock-hyperlink-source"
            echo haddockScript OK
          '';
        };
      };
    in flake1 // {
      # Built by `nix build .`
      defaultPackage = flake.packages."telomare:exe:telomare-exe";
      checks = {
        build = self.defaultPackage.x86_64-linux;
        telomareTest0 = flake.packages."telomare:test:telomare-test";
        telomareTest1 = flake.packages."telomare:test:telomare-parser-test";
        telomareTest2 = flake.packages."telomare:test:telomare-serializer-test";
      };

      # This is used by `nix develop .` to open a shell for use with
      # `cabal`, `hlint` and `haskell-language-server`
      devShell = pkgs.telomare.shellFor {
        tools = {
          cabal = "latest";
          hlint = "latest";
          haskell-language-server = "latest";
          ghcid = "latest";
        };
      };
    });
}
