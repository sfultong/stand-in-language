{ rev ? "78d05675a4186c3b7b2de214f3c3b245ba0d2fa5",
  # rev ? "1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a",
  outputSha256 ? "0aam50m1w1kqfdhwnazzi6jdq422d3ib3ilvb1m5lcr5jn7nhf1f",
  # enableLLVMAssertions ? true
  enableLLVMAssertions ? false
}:

with rec {
  # nixpkgs = (import <nixpkgs> { }).fetchFromGitHub {
  nixpkgs = builtins.fetchTarball {
    # a = true;
    # owner = "NixOS";
    # repo = "nixpkgs";
    # rev = rev1;
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = outputSha256;
  };
  # pkgs_not_used = import nixpkgs {
  pkgs = import nixpkgs {
    overlays = [(self: super: {
      llvm_8 = super.llvm_8.overrideAttrs (oldAttrs: {
          cmakeFlags =
            if enableLLVMAssertions
              then ["-DLLVM_ENABLE_ASSERTIONS=ON"] ++ oldAttrs.cmakeFlags
              else oldAttrs.cmakeFlags;
      });
    })];
  };
  # pkgs = import nixpkgs {};

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
      llvm-hs = super.callHackage "llvm-hs" "8.0.0" { llvm-config = pkgs.llvm_8; };
      llvm-hs-pure = super.callHackage "llvm-hs-pure" "8.0.0" {};
    };
  });
  simpleShell = haskellPkgs.shellFor { packages = p: [p.telomare]; };

}; simpleShell.overrideAttrs (oldAttrs : rec
  { buildInputs = oldAttrs.buildInputs
    ++ [
         haskellPkgs.cabal-install
         haskellPkgs.apply-refact
         haskellPkgs.hlint
         haskellPkgs.hasktags
         haskellPkgs.haddock
      ];
  })
