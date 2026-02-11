# Contributing to Issy

As this is a small academic project, we do not have any strict rules on how you can contribute to Issy. The easiest way to get into this is to email Philippe or Rayna. However, to make things as accessible as possible, we want to lay out how the project is structured and what standards (we try to) maintain.

You might want to start by building the HTML version of the documentation. The first time you do this, run
```
    stack haddock --haddock-internal
```
This will build the full [haddock](https://haskell-haddock.readthedocs.io/) documentation. After that, you can run
```
    make documentation
```
which will build the documentation for all of Issy's internal modules.

If you do not know where to start looking exactly, you can start by exploring from the `Issy`, `Issy.Logic.FOL`, `Issy.Solver.ObjectiveSolver`, and `Issy.Prelude` modules. Those cover important modules for different parts of the project.

## Code Style and Quality

We try to maintain a certain standard for code style and want to incentivize you to do the same.
The main goal is to make the code future-proof and prevent academic code rot.
In addition, one needs to keep in mind that not everybody who wants to work with this might be a Haskell expert.

- *Documentation*: We use [haddock](https://haskell-haddock.readthedocs.io/) for documentation. Every module should have a documentation header, and all exports should be documented.

- *Formatting*: In order to keep the code in a uniform style, we use the [hindent](https://hackage.haskell.org/package/hindent) auto-formatter with a line length of 100. You can format the entire codebase by running `make format`. Try to use the newest version of hindent.

- *Linting*: We use [hlint](https://github.com/ndmitchell/hlint) for linting. You can run the pre-configured version of linting by running `make lint`. All suggestions from hlint for this configuration should be implemented.

- *Imports/exports*: All modules should explicitly indicate what they export. Imports should, in almost all cases, be either an explicit import list or qualified, with `Issy.Prelude` being a notable exception. When doing qualified imports, use a short name instead of a long one, e.g., `Set` instead of `Data.Set`. For common data structures like `Map` or `Set`, the functions should usually be imported qualified. Seldom can a module be imported unqualified without explicit imports if it is a data module for a sub-part that is not used outside of this.

- *Safe Haskell*: All modules that are part of Safe Haskell should be marked as such with the `SAFE` language pragma.

- *Language Extensions*: We try to limit the use of language extensions to ones that provide simple syntactic extensions like `LambdaCase` or `MultiWayIf`. Extensions that extend the type-system or feature set significantly, like `ImplictParameters` or `TemplateHaskell`, should be avoided wherever possible.
