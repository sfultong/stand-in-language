{ rev ? "78d05675a4186c3b7b2de214f3c3b245ba0d2fa5",
  outputSha256 ? "0aam50m1w1kqfdhwnazzi6jdq422d3ib3ilvb1m5lcr5jn7nhf1f",
  enableLLVMAssertions ? true
}:

with rec {
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = outputSha256;
  };
  pkgs_not_used = import nixpkgs {
    overlays = [(self: super: {
      llvm_8 = super.llvm_8.overrideAttrs (oldAttrs: {
          cmakeFlags =
            if enableLLVMAssertions
              then ["-DLLVM_ENABLE_ASSERTIONS=ON"] ++ oldAttrs.cmakeFlags
              else oldAttrs.cmakeFlags;
      });
    })];
  };
  pkgs = import nixpkgs {};
  telomare_jumper = pkgs.stdenv.mkDerivation {
    name = "telomareJumper";
    src = ./cbits;
    buildInputs = [pkgs.boehmgc];
  };
  haskellPkgs = with pkgs.haskell.lib; pkgs.haskell.packages.ghc865.override(old: {
    all-cabal-hashes = builtins.fetchurl {
      url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/1de0d224fe9c8e8947f217c92a12d9249334c5e4.tar.gz";
      sha256 = "1ycayni4pjmgki8cdhcg25bmw970289f89b62sbdzw5naw15rrb1";
    };
    overrides = self: super: {
      telomare = super.callCabal2nix "telomare" ./. { gc = pkgs.boehmgc; jumper = telomare_jumper; };
      # llvm-hs = super.callHackage "llvm-hs" "8.0.0" { llvm-config = pkgs.llvm_8; };
      # llvm-hs-pure = super.callHackage "llvm-hs-pure" "8.0.0" {};

      ghcide = pkgs.haskell.lib.dontCheck (super.callCabal2nix
        "ghcide"
        (builtins.fetchGit {
          url = "https://github.com/digital-asset/ghcide.git";
          rev = "0838dcbbd139e87b0f84165261982c82ca94fd08";
        })
        {});
      hie-bios = pkgs.haskell.lib.dontCheck (super.callHackageDirect {
        pkg = "hie-bios";
        ver = "0.3.2";
        sha256 = "08b3z2k5il72ccj2h0c10flsmz4akjs6ak9j167i8cah34ymygk6";
      } {});
      haskell-lsp = pkgs.haskell.lib.dontCheck (super.callHackageDirect {
        pkg = "haskell-lsp";
        ver = "0.18.0.0";
        sha256 = "0pd7kxfp2limalksqb49ykg41vlb1a8ihg1bsqsnj1ygcxjikziz";
      } {});
      haskell-lsp-types = pkgs.haskell.lib.dontCheck (super.callHackageDirect {
        pkg = "haskell-lsp-types";
        ver = "0.18.0.0";
        sha256 = "1s3q3d280qyr2yn15zb25kv6f5xcizj3vl0ycb4xhl00kxrgvd5f";
      } {});
      # shake = pkgs.haskell.lib.dontCheck (super.callHackage "shake" "0.18.3" {});
    };
  });

  NIX_GHC_LIBDIR = "${haskellPkgs.ghc}/lib/ghc-${haskellPkgs.ghc.version}";
  LD_LIBRARY_PATH = "$LD_LIBRARY_PATH:/usr/lib/";

  simpleShell = haskellPkgs.shellFor { packages = p: [p.telomare]; };

}; simpleShell.overrideAttrs (oldAttrs : rec
  { buildInputs = oldAttrs.buildInputs
    ++ [
         haskellPkgs.cabal-install
         haskellPkgs.apply-refact
         haskellPkgs.hlint
         haskellPkgs.ghcide
         haskellPkgs.ghcid
         haskellPkgs.hasktags
         haskellPkgs.haddock
         pkgs.gmp
         pkgs.zlib
         pkgs.ncurses
         # pkgs.stack
      ];
  })
