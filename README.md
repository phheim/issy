# Issy

Issy is a tool for the automatic synthesis of inifinite-state reactive programs. 

TODO: link to the different file formats somewhere

## Perquisites

To build Issy, the following is needed: 
- [Haskell Stack](https://www.haskellstack.org/): Installing Stack can be done either by [GHCUp](https://www.haskell.org/ghcup/) (recommended), the description on Stacks website or the your systems package manager (not recommended). 
- [Z3](https://github.com/Z3Prover/z3): You can install Z3 with your package manager or by downloading the binary from the projects GitHub releases. We recommend using a newer version of Z3 if possible (e.g. 4.13.3). Note that Issy does interact with Z3 via the textual SMTLib2 interface such that the development version or header files are not needed. Also, Issy allows to set the path to a specific binary of Z3.
- [MuVal/Coar](https://github.com/hiroshi-unno/coar) (*OPTIONAL*): MuVal of Coar is need if issy's monitor base pruning (``--pruning``) is used. We recommend used the commit TODO. More instruction can be found here.

## Building

To build Issy, just run
```
    make 
```
in the top-level folder. Stack will take care of getting the respective source code libraries and the compiler so you need to have internet access for that. The ``issy`` binary is placed in the top-level folder of the project. To get a clean build run
```
    make clean
```

## Usage

TODO How to use tools

## Publications

TODO
