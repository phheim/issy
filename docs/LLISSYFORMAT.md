# Low-Level Format for Synthesis of Infinite-State Reactive Systems 

This document describes the Low-Level Format for Synthesis of Infinite-State Reactive Systems (LLissy). This document is still preliminary and might change upon discussion with the academic community. A simple example can be found [here](./sample.llissy).

The goals of the development of the LLissy format include:
- Having a common format for the specification of synthesis problems for infinite-state reactive systems.
- The format should be able to express in a natural way benchmarks from both existing synthesis specification types: games and  temporal logic formulas.
- The format should be stable so that tools can be used and compared to each other reliably in the long term.
- The format should be easy to parse without external libraries to lift the burden on the tool developers.
- The format should still be human-readable to some extent.

The non-goals for LLissy are:
- The format should not necessarily make it easy for humans to write specifications.
- The format should not include syntactic sugar.
- The format should not try to avoid syntactic clutter.

A higher-level format should be used by specification designers to write benchmarks. Such a format would have syntactic sugar and might evolve faster over time to accommodate specifiers' needs. The intention is that higher-level format(s) would be compiled down to LLissy. A common usage chain should therefore be:
```
    Specifier -> High-level format -> Compiler -> LLissy -> Synthesis tool -> Result
```

## Specification Formalism

As a formalism we use RP-LTL and the symbolic games from the paper [*Translation of Temporal Logic for Efficient Infinite-State Reactive Synthesis*](https://doi.org/10.1145/3704888).

## Grammar

In order to be easy to parse, readable with reasonable effort, and to be similar to the SMTLib format, the LLissy uses s-expressions.

Only single-line comments exist which start with ';' and span to the end of the line. Newlines are '\r\n', '\n\r', '\r', and '\n'. However, when generating LLissy automatically '\n' should be used. Similarly ' ' (Space) and '\t' (Tabs) are both non-newline white-spaces. However, only ' ' should be used upon generation. The following productions define identifiers and natural numbers.
```
ALPHA : 'a'...'z' | 'A'...'Z'
DIGIT : '0'...'9'
ID    : ALPHA (ALPHA | DIGIT | '_')*
PID   : ID ['~']
NAT   : DIGIT+
RAT   : DIGIT+ '.' DIGIT+
```
Note that all of these should be parsed greedily until a white-space, '(', ')', or the end-of-file occurs.

A LLissy specification consists of lists of variable declarations, formula specifications, and game specifications. The variables declarations include all variables used in all games and formulas. 
The formula and game specifications are interpreted conjunctively. 
However, at most one game or formula can be a non-safety game or non-safety formula.
```
SPEC : '(' '(' VARDEC* ')' '(' FSPEC* ')' '(' GSPEC*  ')' ')'
```

A variable declaration declares an input or state variable and its respective type
```
VARDEC  : '(' 'input' TYPE ID ')' | '(' 'state' TYPE ID ')'
TYPE    : 'Int' | 'Bool' | 'Real'
``` 

A formula specification is a pair of assumption and guarantee lists. Each element is an RP-LTL formula.
The assumptions come first, and each of the two lists is interpreted as a conjunction. 
```
FSPEC   : '(' '(' FORMULA* ')' '(' FORMULA* ')' ')'
FORMULA : '(' 'ap' TERM ')' | '(' UOP FORMULA ')' | '(' BOP FORMULA FORMULA ')' | (NOP FORMULA*)
UOP     : 'X' | 'F' | 'G' | 'not'
BOP     : 'U' | 'W' | 'R'
NOP     : 'and' | 'or'
```

A game specification consists of a list of location definitions, transition definitions from one location to another location, and an objective definition.
The objective defines the initial location and the winning condition. Each location is annotated with a natural number. For Safety, Reachability, Buechi, and CoBuechi a location is safe, target, Buechi accepting, coBuechu accepting (should be visited eventually always), iff the number is greater than zero. For ParitMaxOdd the number is the color in the parity game.
```
GSPEC    : '(' '(' LOCDEF* ')' '(' TRANSDEF* ')' OBJ ')'
LOCDEF   : '(' ID NAT TERM ')'
TRANSDEF : '(' ID ID TERM ')'
OBJ      : '(' ID ('Safety' | 'Reachability '| 'Buechi' | 'CoBuechi' | 'ParityMaxOdd') ')'
```

A term is basically like in the SMTLib format without quantifiers, lambda, and let expressions. Similar rules for typing apply.
Only variables declared initially are allowed to be free variables, and additionally primed version (with ~) of the state variables.
```
TERM   : '(' OP TERM* ')' | PID | CONSTS
OP     : 'and ' | 'or' | 'not' | 'ite' | 'distinct' | '=>' |
         '=' | '<' | '>'| '<=' | '>=' |
         '+' | '-' | '*' | '/' | 'mod' | 'abs' | 'to_real' 
CONSTS : RAT | NAT | 'true' | 'false'
```
