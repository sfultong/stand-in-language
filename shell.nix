{ rev ? "95a8cb3ade1ad0e2649f0f3128e90c53964af5e1",
  outputSha256 ? "0jxn25l8d65h6qnmx9f4dsi2fscqyxc0gvhnkj1bc7kicn9rr5hj",
  enableLLVMAssertions ? true
}:
let
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = outputSha256;
  };
  pkgs = import nixpkgs {
    overlays = [(self: super: {
      llvm_6 = super.llvm_6.overrideAttrs (oldAttrs: {
          cmakeFlags =
            if enableLLVMAssertions
              then ["-DLLVM_ENABLE_ASSERTIONS=ON"] ++ oldAttrs.cmakeFlags
              else oldAttrs.cmakeFlags;
      });
    })];
  };
  sil_jumper = pkgs.stdenv.mkDerivation {
    name = "silJumper";
    src = ./cbits;
  };
  haskellPkgs = with pkgs.haskell.lib; pkgs.haskell.packages.ghc843.override(old: {
    all-cabal-hashes = builtins.fetchurl {
      url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/cc4387cface30e2720afff1cd7c412c43317e996.tar.gz";
      sha256 = "16agk33n7kzz5hdjq805mpdcv0cvgxqkvjb5ipq7bn7ahqw0lfil";
    };
    overrides = self: super: {
      sil = super.callCabal2nix "sil" ./. { jumper = sil_jumper; };
      llvm-hs = super.callHackage "llvm-hs" "6.3.0" { llvm-config = pkgs.llvm_6; };
      llvm-hs-pure = super.callHackage "llvm-hs-pure" "6.2.1" {};
      indents = dontCheck super.indents;
    };
  });
in
haskellPkgs.shellFor {
  packages = p: [p.sil];
}
