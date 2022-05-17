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
    flake-utils.lib.eachDefaultSystem (system:
      with nixpkgs.legacyPackages.${system};
      let
        t = lib.trivial;
        hl = haskell.lib;

        name = "telomare";
	compiler = pkgs.haskell.packages."ghc922";

        project = devTools: # [1]
          let addBuildTools = (t.flip hl.addBuildTools) devTools;
          in compiler.developPackage {
            root = lib.sourceFilesBySuffices ./. [ ".cabal" ".hs" ];
            name = name;
            returnShellEnv = !(devTools == [ ]); # [2]

            modifier = (t.flip t.pipe) [
              addBuildTools
              # hl.dontHaddock
            ];
          };

      in {
        packages.pkg = project [ ]; # [3]

        defaultPackage = self.packages.${system}.pkg;

        devShell = project (with compiler; [ # [4]
          cabal-install
          # haskell-language-server # uncomment when support for 9.2.2 comes out
          hlint
	  ghcid
	  stylish-haskell
        ]);
	
	checks = {
          build = self.defaultPackage.x86_64-linux;
          telomareTest0 = flake.packages."telomare:test:telomare-test";
          telomareTest1 = flake.packages."telomare:test:telomare-parser-test";
          telomareTest2 = flake.packages."telomare:test:telomare-serializer-test";
	};
      });
}
