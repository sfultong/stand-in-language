# Stand-in Language
> The Non-Turing Complete Language that helps you reason about termination time and other metrics

[![Join the chat at https://gitter.im/stand-in-language/Lobby](https://badges.gitter.im/stand-in-language/Lobby.svg)](https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This proyect is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Quick Start

0. Clone this repository and change directory to it:
   ```
   $ git clone https://github.com/sfultong/stand-in-language.git
   $ cd stand-in-language
   ```
1. [Install Nix](https://nixos.org/nix/download.html):
   ```
   $ curl https://nixos.org/nix/install | sh
   ```
2. Enter a Nix shell. This will setup an enviroment where all external dependancies are available (such as `cabal` for building):
   ```
   $ nix-shell shell.nix
   ```
3. Build the proyect:
   ```
   $ cabal v2-build
   ```
4. Run the tictactoe example and start playing with a friend:
   ```
   $ cabal v2-run sil-exe
   ```

## Running your own SIL code
1. Create your own file with the sil code
2. Modify the last uncommented line to reference your file.
   ```haskell
   Strict.readFile "<your-sil-code-file>.sil" >>= runMain
   ```
3. Run:
   ```
   $ nix-shell shell.nix
   $ cabal v2-build
   $ cabal v2-run sil-exe
   ```
   
## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. ![A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. ![SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. ![Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/sfultong/stand-in-language/blob/master/LICENSE).
