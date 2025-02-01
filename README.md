# Issy

Issy is a tool for the automatic synthesis of infinite-state reactive programs. It accepts specifications in the [Issy format](./docs/ISSYFORMAT.md) as well as reactive program games, TSL-MT, and the low-level [LLissy format](./docs/LLISSYFORMAT.md). 

## Installation

### Perquisites

To build Issy, the following is needed: 
- [Haskell Stack](https://www.haskellstack.org/): Installing Stack can be done either by [GHCUp](https://www.haskell.org/ghcup/) (recommended), the description on Stacks website or the your systems package manager (not recommended). 
- [Z3](https://github.com/Z3Prover/z3): You can install Z3 with your package manager or by downloading the binary from the projects GitHub releases. We recommend using a newer version of Z3 if possible (e.g. 4.13.3). Note that Issy does interact with Z3 via the textual SMTLib2 interface such that the development version or header files are not needed. Also, Issy allows to set the path to a specific binary of Z3.
- [Spot](https://spot.lre.epita.fr/) (*OPTIONAL but HIGHLY RECOMMENDED*): If you want to use temporal logic formulas you need ``ltl2tgba`` from Spots Omega-automata tool-suite.
- [MuVal/Coar](https://github.com/hiroshi-unno/coar) (*OPTIONAL*): MuVal of Coar is need if Issy's monitor base pruning (``--pruning``) is used. We recommend using commit dc094f04 for now. More instruction can be found in the *External Tools* section.

### Building

To build Issy, just run
```
    make 
```
in the top-level folder. Stack will take care of getting the respective source code libraries and the compiler so you need to have internet access for that. The ``issy`` binary is placed in the top-level folder of the project. To get a clean build run
```
    make clean
```

## Usage

The general ways of using Issy is
```
    ./issy [OPTIONS] FILENAME
```
The output (e.g. Realizable/Unrealizable, synthesized program) are always written to ``STDOUT``. Logging and error informations are output on ``STDERR``. The input is either read from a file or from ``STDIN`` if the filename is ``-``.
The **list of all options** –from the following explanation as well as minor options– can be accessed via **``--help``**.

Issy supports different file-formats: 
- On ``--issy`` it expects a file in the [Issy format](./docs/ISSYFORMAT.md). This is the *default*.
- On ``--llissy`` the expected input is in the [LLIssy format](./docs/LLISSYFORMAT.md).
- On ``--rpg`` the expected input is a reactive program game in the ``.rpg`` format.
- On ``--tslmt`` the input in in the TSL-MT dialect used by ``tslmt2rpg``.

Issy operates in different *modes*, especially it can stop and output at each steps of its pipeline:
- For ``--compile`` Issy takes an input in the Issy format and compiles it to the LLissy format.
- For ``--to-game`` Issy takes any input and translates it to a single synthesis game, possibly using monitor-simplifications depending on the pruning level. Note that ``ltl2tgba`` is needed if the input contains temporal logic formulas. For Issy and LLissy specifications the this results in a LLissy specification with a single synthesis game and no RP-LTLT formulas.  Otherwise, if the inputs is a TSL-MT (or RPG) specification this will result in an RPG specification (Warning: The later part might change in the future!).
- For ``--solve`` Issy translates the input to a synthesis game (if necessary) and then solves this game. This is the *default* mode. By default it also only check for realizability. In order to produce a program for realizable inputs, use  ``--synt``, additionally.

Issy can generate a lot of logging informations which allows to follow the solving and synthesis process in detail. 
The options, ``--quiet ``, ``--info``, ``--detailed``, and ``--verbose``, allow to get no logging at all to every attractor step and every SMT call. 
Furthermore, Issy generates some summarizing statistics at the end, which are part of the log. ``--stats-to-stdout`` allows them to be part of the output.


### Translation and Solving 

Issy allows more control over the translation and solving process. For the translation from a temporal logic formulas to a game, you can set the amount of monitor pruning with ``--pruning LEVEL``: 
- On ``--pruning 0`` monitor simplifications are disabled, which is the *default*. Use this if the temporal formula is relatively simple or does not contain intricate connections in itself. If unsure try first as monitor simplification can create a significant overhead.
- On ``--pruning 1`` monitor simplifications are enabled without any deduction rules and few propagation of predicates.
- On ``--pruning 2`` monitor simplifications are enabled and use the standard deduction rules and a decent amount of propagation of predicates. This is a good option if level 0 does not apply. *It requires MuVal*.
- On ``--pruning 3`` all monitor simplification rules are enabled, including precise deduction, as well as a maximum amount of propagation of predicates. This will likely incur a large overhead and *it requires Coars MuVal and MaxCHC*.

For game solving ``--accel TYPE`` controls what type of acceleration is used. For ``no`` acceleration is disabled, for `` attr`` only attractor acceleration is enabled (which the recommended *default*), and for ``full`` also the outer fix-point accelerations are enabled, like Büchi acceleration. 
Attractor acceleration can further be controlled via ``--accel-attr TYPE``.
- For ``--accel-attr geom`` geometric attractor acceleration is used. This is the *default*.
- For ``--accel-attr geom`-ext` the former is used with extended invariant computation techniques.
- For ``--accel-attr unint`` uninterpreted-function-base attractor acceleration is used.
- For ``--accel-attr unint-ext`` the former is used with potential nesting of acceleration.
In addition, ``--accel-difficulty LEVELS`` lets you control the "aggressiveness" of the acceleration. The higher the more likely acceleration is to succeed, but the more time it might take. The levels are ``easy``, ``medium``, and ``hard`` with ``medium`` being the recommended *default*.

### External Tools

Issy uses different external tools, which are need for different operations. Some of them have to be called via a wrapper script. In all cases by *default* the Issy assumes tool or wrapper script to be in the PATH environment. If this is not desired, you can also set the location to the binary/script to the respective tool manually:
- ``--caller-z3 PATH`` set the path to the Z3 binary. By default ``z3`` is assumed to be in the PATH.
- ``--caller-aut PATH``set the path to spots ``ltl2tgba``. By default ``ltl2tgba`` is assumed to be in the PATH.
- ``--caller-muval PATH`` set the path to a script that reads its input on (it's) STDIN and a tiemout in seconds as argument, and calls MuVal on the input with the respective timeout.
- ``--caller-chcmx  PATH`` set the path to a script that reads its input on (it's) STDIN and a tiemout in seconds as argument, and calls CHCMax on the input with the respective timeout.
Example for those wrapper scripts can be found TODO.

## Related Publications and Documents

- [*Translation of Temporal Logic for Efficient Infinite-State Reactive Synthesis*](https://doi.org/10.1145/3704888), Philippe Heim, Rayna Dimitrova, POPL2025.  
- [*Localized Attractor Computations for Infinite-State Games*](https://doi.org/10.1007/978-3-031-65633-0_7), Anne-Kathrin Schmuck, Philippe Heim, Rayna Dimitrova, Satya Prakash Nayak, CAV2024.
- [*Solving Infinite-State Games via Acceleration*](https://doi.org/10.1145/3632899), Philippe Heim, Rayna Dimitrova, POPL2024.
- [POPL24 Talk](https://youtu.be/3G0WaerPZpQ)
