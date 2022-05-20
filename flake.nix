{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let pkgs = import nixpkgs { inherit system; };
          t = pkgs.lib.trivial;
          hl = pkgs.haskell.lib;
          compiler = pkgs.haskell.packages."ghc922";
          project = executable-name: devTools: # [1]
            let addBuildTools = (t.flip hl.addBuildTools) devTools;
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
                hl.doCheck
                addBuildTools
                # hl.dontHaddock
              ];
            };

      in {
        packages.telomare = project "telomare" [ ]; # [3]
        packages.default = self.packages.${system}.telomare;

        defaultApp = self.packages.${system}.telomare;

        devShells.default = project "telomare" (with compiler; [ # [4]
          cabal-install
          # haskell-language-server # uncomment when support for 9.2.2 comes out
          hlint
	        ghcid
	        stylish-haskell
        ]);
	
        checks = {
          build = self.packages.${system}.default;
          test-suit = project "telomare-test" [ ];
          parser-test-suit = project "telomare-parser-test" [ ];
          serializer-test-suit = project "telomare-serializer-test" [ ];
        };
      });
}
