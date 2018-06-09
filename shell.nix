let
  debug = true;
  pkgs = if debug then import /home/sfultong/temp/nixpkgs {} else import <nixpkgs> {};

  silEnv = { mkDerivation, base, llvm-hs, llvm-hs-pure, bytestring, binutils, stdenv
           , indents, containers, mtl, parsec, QuickCheck, recursion-schemes, strict } : mkDerivation
  {
    pname = "silEnv";
    src = ./src;
    version = "0.1.0";
    license = stdenv.lib.licenses.asl20;
    isExecutable = true;
    isLibrary = true;
    librarySystemDepends = [ binutils ];
    libraryHaskellDepends =
     [ base bytestring containers indents llvm-hs llvm-hs-pure mtl parsec recursion-schemes
     ];
    executableHaskellDepends = [ base containers strict ];
    testHaskellDepends = [ base QuickCheck strict ];
  };

  drv = pkgs.haskellPackages.callPackage silEnv {};

in if pkgs.lib.inNixShell then drv.env else drv
