{ compiler ? "ghc822" }:

let
  debug = false;
  pkgs = if debug then import /home/sfultong/temp/nixpkgs {} else import <nixpkgs> {};

  sil_jumper = with pkgs; stdenv.mkDerivation {
    name = "silJumper";
    buildInputs = [ stdenv clang ];
    src = ./cbits;
  };
  silEnv = { mkDerivation, base, llvm-hs, llvm-hs-pure, bytestring, llvm_6, binutils, stdenv
           , indents, containers, mtl, parsec, QuickCheck, recursion-schemes, strict, vector
           , hspec, criterion, derive-storable, derive-storable-plugin} : mkDerivation
  {
    pname = "silEnv";
    src = ./src;
    version = "0.1.0";
    license = stdenv.lib.licenses.asl20;
    isExecutable = true;
    isLibrary = true;
    librarySystemDepends = [ binutils sil_jumper llvm_6];
    libraryHaskellDepends =
     [ base bytestring containers indents llvm-hs llvm-hs-pure mtl parsec recursion-schemes
       vector hspec criterion derive-storable derive-storable-plugin
     ];
    executableHaskellDepends = [ base containers strict ];
    testHaskellDepends = [ base QuickCheck strict ];
  };
  haskellPkgs = pkgs.haskell.packages."${compiler}".extend(
      self: super: {
          indents = pkgs.haskell.lib.dontCheck super.indents;           
          llvm-hs-pure = super.callHackage "llvm-hs-pure" "5.1.2" {}; 
          llvm-hs      = super.callHackage "llvm-hs" "5.1.3" { llvm-config = pkgs.llvm_5; }; 
      });
  drv = haskellPkgs.callPackage silEnv {};

in if pkgs.lib.inNixShell then drv.env else drv
