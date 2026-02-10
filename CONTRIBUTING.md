# Contributing to Issy

As this is a small academic project, we do not have any strict rules how you can contribute to Issy. The easiest way to get into this is to just write Philippe or Rayna an e-mail. However, in order to make thing as accessible as possible, we want to lay-out how the project is structured and what kind of standards (we try to) maintain. 

You might want to start by building the HTML version of the documentation. The first time you do this, run
```
    stack haddock --haddock-internal
```
This will build the full [haddock](https://haskell-haddock.readthedocs.io/) documentation. After that you can run
```
    make documentation
```
which will build the documentation for all of Issy's internal modules.

## Structure or "Where should I start looking"


Especially: Issy, Issy.Prelude, Logic.FOL

TODO: Lay out structure. 

## Code Style and Quality

TODO: write out. Goals are look term viability, clean code.

- Documentation: We use haddock. We strive to keep those complete and so should you.

- Formatting: We use hindent as the auto formatter (with a line width of 100). Ideally the newest version. Call `make format` to format everything.

- Linting: We use hlint as the linter. Run `make lint` to lint everything.

- Imports and exports: Explicit export list. Imports have to be either qualified for a shortened name or explicit import list. Exception are "Issy.Prelude" and seldomely internal modules.

- No fancy language features: Syntacic stuff like "LambdaCase, MultWayIf" fine. Avoid "Template Haskell", "Implicit Paramters" -- not very newcomer friendly. 
