{ # Fetch the latest haskell.nix and import its default.nix
  haskellNix ? import (builtins.fetchTarball "https://github.com/input-output-hk/haskell.nix/archive/ef6ca0f431fe3830c25cb2d185367245c1cce894.tar.gz") {}
  # haskellNix ? import (builtins.fetchTarball "https://github.com/input-output-hk/haskell.nix/archive/master.tar.gz") {}

  # # For LLVM
  # , enableLLVMAssertions ? true # TODO: Fix

, compiler ? "ghc884"
}:
let
  # haskell.nix provides access to the nixpkgs pins which are used by our CI,
  # hence you will be more likely to get cache hits when using these.
  # But you can also just use your own, e.g. '<nixpkgs>'.
  nixpkgsSrc = haskellNix.sources.nixpkgs-2003;

  # haskell.nix provides some arguments to be passed to nixpkgs, including some
  # patches and also the haskell.nix functionality itself as an overlay.
  nixpkgsArgs = haskellNix.nixpkgsArgs;

  telomare_jumper = pkgs.stdenv.mkDerivation {
    name = "telomareJumper";
    src = ./cbits;
    buildInputs = [ pkgs.boehmgc ];
  };

  telomareOverlays = [ (self: super: {
    jumper = telomare_jumper;
    gc = self.boehmgc;
    llvm-config = self.llvm_9;
    alex = self.haskellPackages.alex;
  }) ];

  # import nixpkgs with overlays
  pkgs = (import nixpkgsSrc (nixpkgsArgs // { overlays = nixpkgsArgs.overlays ++ telomareOverlays;}));
in
pkgs.haskell-nix.cabalProject {
  src = pkgs.haskell-nix.cleanSourceHaskell {
    src = ./.;
    name = "telomare";
  };
  compiler-nix-name = compiler;
  pkg-def-extras = with pkgs.haskell.lib; [
     (hackage: {
       llvm-hs = hackage.llvm-hs."9.0.1".revisions.default;
       llvm-hs-pure = hackage.llvm-hs-pure."9.0.0".revisions.default;
     })
   ];
  modules = [
    { reinstallableLibGhc = true; }
  ];
}
