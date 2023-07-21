{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    hvm.url = "github:hhefesto/HVM";
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, hvm }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-linux" ] (system:
      let pkgs = import nixpkgs { inherit system; };
          t = pkgs.lib.trivial;
          hl = pkgs.haskell.lib;
          compiler = pkgs.haskell.packages."ghc924";
          project = runTests: executable-name: devTools: # [1]
            let addBuildTools = (t.flip hl.addBuildTools) devTools;
                addBuildDepends = (t.flip hl.addBuildDepends)
                  [ hvm.defaultPackage.${system} ];
                doRunTests =
                  if runTests then hl.doCheck else hl.dontCheck;
            in compiler.developPackage {
              root = pkgs.lib.sourceFilesBySuffices ./.
                       [ ".cabal"
                         ".hs"
                         ".tel"
                         "cases"
                         "LICENSE"
                       ];
              name = executable-name;
              returnShellEnv = !(devTools == [ ]); # [2]

              modifier = (t.flip t.pipe) [
                addBuildDepends
                addBuildTools
                doRunTests
                # hl.dontHaddock
              ];
            };

      in {
        packages.telomare = project false "telomare" [ ]; # [3]
        packages.default = self.packages.${system}.telomare;

        apps.default = {
          type = "app";
          program = self.packages.${system}.telomare + "/bin/telomare";
        };

        apps.repl = {
          type = "app";
          program = self.packages.${system}.telomare + "/bin/telomare-repl";
        };

        devShells.default = project false "telomare-with-tools" (with compiler; [ # [4]
          cabal-install
          haskell-language-server
          hlint
          ghcid
          stylish-haskell
          hvm.defaultPackage.${system}
        ]);
	
        checks = {
          build-and-tests = project true "telomare-with-tests" [ ];
        };
      });
}
