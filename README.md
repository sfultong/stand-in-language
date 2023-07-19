# Telomare
> A simple but robust virtual machine

<p float="left">
  <img src="https://github.com/Stand-in-Language/stand-in-language/actions/workflows/telomare-ci.yml/badge.svg" />
  <a href="https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge"
     title="Join the chat at https://gitter.im/stand-in-language/Lobby">
    <img src="https://badges.gitter.im/stand-in-language/Lobby.svg" /> 
  </a>
</p>


A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This project is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Quick Start

1. Clone this repository and change directory to it:
   ```
   $ git clone https://github.com/Stand-In-Language/stand-in-language.git
   $ cd stand-in-language
   ```
2. [Install Nix](https://nixos.org/nix/download.html):
   ```
   $ curl https://nixos.org/nix/install | sh
   ```
3. Optional (reduces build time by using telomare's cache):
   ```
   # Install cachix with nix-env or adding `cachix` to your `/etc/nixos/configuration.nix`'s' `environment.systemPackages` if in NixOS.
   $ nix-env -iA cachix -f https://cachix.org/api/v1/install
   $ cachix use telomare
   ```
4. Enter a Nix shell. This will setup an environment where all external dependencies will be available (such as `cabal` for building):
   ```
   $ nix-shell shell.nix
   ```
5. Build the project:
   ```
   $ cabal new-build
   ```
6. Run the tictactoe example and start playing with a friend (or run your own telomare file):
   ```
   $ cabal new-run telomare -- tictactoe.tel
   ```
7. Profit!

## Running `cabal new-repl`

There is a known issue (#7) for getting a repl.

To get around it, you should copy `libgc.so.1` (provided by the `bohem` garbage collector) into your repository (telomare/lib is a good choice) and rename it to `libgc.so`. You will also need to reference it on `telomare.cabal` under the `library` stanza. Be sure to use the complete path for `libgc.so` on `telomare.cabal` (a commented version on `telomare.cabal` is provided as an example).

## Telomare REPL
1. Run:
   ```
   $ cd <your/local/proyect/location>/telomare
   $ nix-shell shell.nix
   $ cabal new-build
   $ cabal new-run telomare-repl -- --haskell
   ```
2. Profit!
   
## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. [A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. [SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. [Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/Stand-In-Language/stand-in-language/blob/master/LICENSE).
