# Issy

Issy is a tool for automatically synthesizing infinite-state reactive programs. It accepts specifications in the [Issy format](./docs/ISSYFORMAT.md), reactive program games, TSL-MT, and the low-level [LLissy format](./docs/LLISSYFORMAT.md).
You can find small examples for Issy and LLIssy [here](./docs/sample.issy) and [here](./docs/sample.llissy), respectively. Furthermore, many more examples are available in the [infinite-state synthesis benchmark repository](https://github.com/phheim/infinite-state-reactive-synthesis-benchmarks).

## Setup

While building Issy from source is pretty easy, in order to run (with the full functionality), you might need to also install Z3, Spot, and MuVal, depending on the functions you want to use. Hence, if you just *want to try Issy*, we recommend using one of our *container setups*. Those should work on ``x86-64`` machines. If you use an Apple Silicon M1 or M2 chip, you need to build Issy from source.

For our container setups, you will need to build and run OCI containers. In our instructions we use [Podman](https://podman.io), which we recommend. However, you should also be able to do the same with other container tools like Docker.

### Container Setup (*RECOMMENDED FOR BEGINNERS*)

The first setup is for you if you just want to get Issy quickly. It includes pre-built binaries for Issy and Z3. It will build Spot but not MuVal. To build the container image, run
```
    podman build -t issy-runner containers/version2/runner-simple
```
This should take around **30 minutes**.
Note that if you want you can also use an older version of Issy by replacing `version-2` by `version-1`.

If you want to use the container, either use our call script
```
    ./containers/run-issy ARGUMENTS < INPUTFILE
```
or run the container directly
```
    podman run -i --rm issy-runner OPTIONS < INPUTFILE
```
The usage and arguments are practically the same as with the Issy binary. The only differences are technical because we run inside a container (the input file is always passed via ``STDIN`` and the ``--caller-...`` options are overwritten in the container).

**Restriction:** As this container setup is missing MuVal, for ``--pruning`` *only levels 0 and 1 work* properly. If you want to include MuVal, you can build the full container with
```
    podman build -t issy-runner containers/version-2/runner-full
```
Note that this will take **around 1.5 hour** and will use significantly more disk space.
Similarly to above, if you want you can also use an older version of Issy by replacing `version-2` by `version-1`.

### Build from Source

To build Issy itself, you need the Haskell build tool [Stack](https://www.haskellstack.org/). To get it, we recommend [GHCUp](https://www.haskell.org/ghcup/).
To build Issy, just run
```
    make
```
in the top-level folder. Stack will get the respective source code libraries and the compiler, so you need internet access for that. The ``issy`` binary is placed in the project's top-level folder. To get a clean build, run ``make clean``.

To run Issy, you also **must** get [Z3](https://github.com/Z3Prover/z3) with **version 4.13.0 or newer**. For now we recommend using [version 4.15.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.15.1). If you want to get this specific version of Z3 or your packages manager does only have an older version of Z3, the easiest way got a difeerent version is to download the binary from its [GitHub releases](https://github.com/Z3Prover/z3/releases) and *tell Issy to use that* with the ``--caller-z3 <PATH_TO_Z3>`` option.

You also **should** get [Spot](https://spot.lre.epita.fr/) as we Issy needs ``ltl2tgba`` from Spots Omega-automata tool suite. To get it just, follow their installation instructions. Using spot will work by default if ``ltl2tgba`` can be found by Issy in your PATH. If you want a different setup check out the ``--caller-aut <PATH_TO_LTL2TGBA>`` option.

You **can** also get [MuVal of Coar](https://github.com/hiroshi-unno/coar) which is needed if Issy's monitor-based ``--pruning`` option on level 2 or higher is used. To get MuVal you must  build it from source (we strongly recommend commit 1d499999) and use (and adapt to the right locations) the wrapper script in ``scripts/call-muval.sh`` which is called with ``--caller-muval <PATH_TO_CALLSCRIPT>``.

## Usage

The general way of using Issy is
```
    ./issy [OPTIONS] FILENAME
```
Issy writes its output (e.g., Realizable/Unrealizable, synthesized program) to ``STDOUT``. Logging and error information are output on ``STDERR``. The input is read from a file or from ``STDIN`` if the filename is ``-``.
The **list of all options** –including the following explanation and minor options– can be accessed via **``--help``**.

Issy supports different file formats:
- On ``--issy`` it expects a file in the [Issy format](./docs/ISSYFORMAT.md). This is the *default*.
- On ``--llissy`` the expected input is in the [LLissy format](./docs/LLISSYFORMAT.md).
- On ``--rpg`` the expected input is a reactive program game in the ``.rpg`` format.
- On ``--tslmt`` the input is in the TSL-MT dialect used by ``tslmt2rpg``.

Issy operates in different *modes*, and it can stop and produce the respective output at the following steps of its pipeline:
- For ``--compile``, Issy takes input in the Issy format and compiles it into the LLissy format.
- For ``--to-game, `` Issy translates any input into a single synthesis game, possibly using monitor simplifications depending on the pruning level. If the input contains temporal logic formulas, note that ``ltl2tgba`` is needed. For Issy and LLissy specifications, this results in a LLissy specification with a single synthesis game and no RP-LTL formulas. Otherwise, if the input is a TSL-MT (or RPG) specification, this will result in an RPG specification (Warning: The latter part might change in the future!).
- For ``--solve``, Issy translates the input to a synthesis game (if necessary) and then solves this game. This is the *default* mode. By default, it only checks for realizability. To produce a program for realizable input specification, use  ``--synt``, in addition to ``--solve``.

Issy can generate a lot of logging information, which allows you to follow the solving and synthesis process in detail.
The options ``--quiet ``, ``--info``, ``--detailed``, and ``--verbose`` allow from no logging at all to logging for every attractor step and every SMT call.
Furthermore, Issy generates some summarizing statistics at the end, which are part of the log. ``--stats-to-stdout`` allows them to be part of the output.


### Translation and Solving

Issy allows more control over the specification translation and game-solving process.


#### Translation

For the translation from temporal logic formulas to a game, you can set the amount of monitor pruning with ``--pruning LEVEL``:
On ``-- pruning 0``, monitor simplifications are disabled, which is the default. Use this if the temporal formula is relatively simple or does not contain intricate connections. If unsure, try first, as monitor simplification can create a significant overhead.
- On ``--pruning 1`` monitor simplifications are enabled without deduction rules and few propagations of predicates.
- On ``--pruning 2``, monitor simplifications are enabled. They use the standard deduction rules and a decent amount of propagation of predicates. This is a good option if level 0 does not apply. *It requires MuVal*.
- On ``--pruning 3``, all monitor simplification rules are enabled, including precise deduction and a maximum amount of propagation of predicates. This will likely incur a significant overhead, and *it requires Coars MuVal and MaxCHC*.


#### Solving

For game solving ``--accel TYPE`` controls the type of acceleration that is used. For ``no`` acceleration is disabled, for `` attr`` only attractor acceleration is enabled (which is the recommended *default*), and for ``full`` also the outer fix-point accelerations are enabled, like Büchi acceleration.
Attractor acceleration can be controlled further via ``--accel-attr TYPE``.
- For ``--accel-attr polycomp`` compositional acceleration from polyhedra is used. This is the *default*.
- For ``--accel-attr polycomp-ext`` compositional acceleration from polyhedra is used with additional nesting.
- For ``--accel-attr geom`` geometric attractor acceleration is used.
- For ``--accel-attr unint`` uninterpreted-function-based attractor acceleration is used.
- For ``--accel-attr unint-ext``, the former is used with potential nesting of acceleration.
In addition, ``--accel-difficulty LEVELS`` lets you control the "aggressiveness" of the acceleration. The higher the level, the more likely acceleration is to succeed, but the more time it might take. The levels are ``easy``, ``medium``, and ``hard`` with ``medium`` being the recommended *default*.

In addition, the ``--enable-summaries`` enables the usage of enforcement summaries. This will often produce a significant overhead at the moment, but allows to solve more classes of problems.


### Auto Translator

Issy implements auto-translators/encodes from the format it supports into other benchmarks formats used by other tools. Note that some of these translators are pretty "direct", i.e. the translation introduced a lot of boilerplate that sometimes could be optimized away. **If you have ideas how to improve these translations, please feel free to reach out to us.**
- ``--encode-muclp`` encodes a specification into a fixpoint-equation system used by (MuVal)[https://github.com/hiroshi-unno/coar].
- ``--encode-ltlmt`` encodes a specification into a LTLMT formula used by (Syntheos)[https://github.com/imdea-software/syntheos].
- ``--encode-sweap`` encodes a specification into a LTL formula over an infinite arena used by (sweap)[https://github.com/shaunazzopardi/sweap].
Note that all these translations work from in principle all possible input specification formats but may fail if some primitive used in the original specification (like a specific function or type) is not supported by the target specification format.


### External Tools (*NOT FOR CONTAINER USERS*)

Issy uses different external tools, which are needed for different operations. Some of them have to be called via a wrapper script. In all cases, by *default*  Issy assumes the used tool or wrapper script to be in the PATH environment. If this is not desired, you can also set the location to the binary/script to the respective tool manually:
- ``--caller-z3 PATH`` sets the path to the Z3 binary. By default, ``z3`` is assumed to be in the PATH.
- ``--caller-aut PATH`` sets the path to Spot's ``ltl2tgba``. By default, ``ltl2tgba`` is assumed to be in the PATH.
- ``--caller-muval PATH`` sets the path to a script that reads its input on (it's) STDIN and a timeout in seconds as an argument, and calls MuVal on the input with the respective timeout.
- ``--caller-chcmx  PATH`` sets the path to a script that reads its input on (it's) STDIN and a timeout in seconds as an argument, and calls CHCMax on the input with the respective timeout.
Examples of those wrapper scripts can be found [here](./scripts).

## Related Publications and Documents

If you want to cite Issy, please [cite](./docs/issy.bib):
- [*Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State Reactive Systems*](https://doi.org/10.1007/978-3-031-98685-7_14), CAV'25

Other works on which Issy directly builds on are:
- [*Translation of Temporal Logic for Efficient Infinite-State Reactive Synthesis*](https://doi.org/10.1145/3704888), POPL'25 ([Talk](https://youtu.be/Mv0oqdhMfZo))
- [*Localized Attractor Computations for Infinite-State Games*](https://doi.org/10.1007/978-3-031-65633-0_7), CAV'24
- [*Solving Infinite-State Games via Acceleration*](https://doi.org/10.1145/3632899), POPL'24 ([Talk](https://youtu.be/3G0WaerPZpQ))

