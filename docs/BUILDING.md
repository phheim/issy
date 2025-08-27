# Building  Issy

To build Issy you, need the following: 
- [Haskell Stack](https://www.haskellstack.org/): Installing Stack can be done either by [GHCUp](https://www.haskell.org/ghcup/) (recommended), the description on Stacks' website, or your systems package manager (*not recommended*). 
- [Z3] (https://github.com/Z3Prover/z3/): You can install Z3 with your package manager or by downloading the binary from the project's GitHub releases. We recommend using a newer version of Z3 (e.g., 4.13.3). Note that Issy interacts with Z3 via the textual SMTLib2 interface, so the development version or header files are not needed. Also, Issy allows you to set the path to a specific binary of Z3.
- [Spot](https://spot.lre.epita.fr/) (*OPTIONAL but HIGHLY RECOMMENDED*): If you want to use temporal logic formulas, you need ``ltl2tgba`` from Spots Omega-automata tool suite.
- [MuVal/Coar](https://github.com/hiroshi-unno/coar) (*OPTIONAL*): MuVal of Coar is needed if Issy's monitor-based pruning (``--pruning``) is used. We recommend using commit dc094f04 for now. More instructions can be found in the *External Tools* section.

### Building

To build Issy, just run
```
    make 
```
in the top-level folder. Stack will get the respective source code libraries and the compiler, so you need internet access for that. The ``issy`` binary is placed in the project's top-level folder. To get a clean build run
```
    make clean
```


