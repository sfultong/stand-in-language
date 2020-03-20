{ rev ? "c47830563954d4ab4e593a9db6275ce828497f52",
  outputSha256 ? "1xqcwzyzimay2kh8nqabi5b0ly3lc50c0w6asqjl0g97nckr2fj0",
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
  sil_jumper = pkgs.stdenv.mkDerivation {
    name = "silJumper";
    src = ./cbits;
    buildInputs = [pkgs.boehmgc];
  };
  haskellPkgs = with pkgs.haskell.lib; pkgs.haskell.packages.ghc882.override(old: {
    all-cabal-hashes = builtins.fetchurl {
      url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/d076b90184525b100d3a61480fe63788290eab2e.tar.gz";
      sha256 = "1nyq64mx65chf7chw7nq72vmxjabviaxc9va7sfk0dr6szzdz91p";
    };
    overrides = self: super: {
      sil = super.callCabal2nix "sil" ./. { gc = pkgs.boehmgc; jumper = sil_jumper; };
      # llvm-hs = super.callHackage "llvm-hs" "8.0.0" { llvm-config = pkgs.llvm_8; };
      # llvm-hs-pure = super.callHackage "llvm-hs-pure" "8.0.0" {};
    };
  });
  simpleShell = haskellPkgs.shellFor { packages = p: [p.sil]; };

}; simpleShell.overrideAttrs (oldAttrs : rec
  { buildInputs = oldAttrs.buildInputs
    ++ [
         haskellPkgs.cabal-install
         haskellPkgs.apply-refact
         haskellPkgs.hlint
         haskellPkgs.hasktags
         # haskellPkgs.haddock
      ];
  })
