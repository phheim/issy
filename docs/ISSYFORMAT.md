# Issy Format

This document describes the high-level format used by the Issy tool. A simple example can be found [here](./sample.issy).

## Syntax
An Issy specification consists of variable declarations, formula specifications, game specifications, and macro definitions for better readability.

```
SPEC     : (VARDECL | LOGICSPEC | GAMESPEC | MACRO)*
```

### Variable Declarations

Variable declarations determine the variables that can be used in the formula and game specifications. A variable declaration specifies whether the variable is input controlled by the environment, or is a state variable controlled by the system. The currently supported data types are bool, int and real. Variables have global scope and can be used in any of the formula and game specifications in the file.

```
VARDECL  : ('input' | 'state') TYPE IDENTIFIER
TYPE     : 'int' | 'bool' | 'real'
```

### Formula Specifications

A formula specification is a list of RPLTL formulas (as defined in the paper [*Translation of Temporal Logic for Efficient Infinite-State Reactive Synthesis*](https://doi.org/10.1145/3704888)), prefixed by the keywords 'assume' and 'assert', denoting constraints on the environment and the system respectively. They use temporal operators (next 'X', eventually 'F', globally 'G', until 'U', weak until 'W', release 'R') like LTL, but with quantifier-free first-order atoms  instead of Boolean propositions. The precedence is like in TLSF. A formula specification is an implication with antecedent the conjunction of the assumptions and consequent the conjunction of the asserts.

```
LOGICSPEC : 'formula' '{' LOGICSTM*  '}'
LOGICSTM  : ('assert' | 'assume') RPLTL
RPLTL     : ATOM | '(' RPLTL ')' | UOPT RPLTL | RPLTL BOPT RPLTL 
UOPT      : '!' | 'F' | 'X' | 'G'
BOPT      : '&&' | '||' | '->' | '<->' | 'U' | 'W' | 'R'
```


### Game Specifications

A game specification defines the type of winning condition and the initial location of the defined game. Locations (which can be thought of as the values of a local program counter) have names, colors (used in the winning condition), and domain terms (which constrain the possible values of the variables). Transition definitions determine the possible transitions between locations. They are labeled by formulas, which specify under what conditions a transition can be taken and what is its effect. 
Location names have local scope -- if a location name appears in multiple games, those are unrelated. The domain formula associated with each location acts like an invariant restricting the set of possible variable valuations in states with this location.

```
GAMESPEC  : 'game' WINCOND 'from' IDENTIFIER '{' ( LOCDEF | TRANSDEF)* '}' 
WINCOND   : 'Safety' | 'Reachability' | 'Buechi' | 'CoBuechi' | 'ParityMaxOdd' 
LOCDEF    : 'loc' IDENTIFIER [NAT] ['with' FORMULA]
TRANSDEF  : 'from' IDENTIFIER 'to' IDENTIFIER 'with' FORMULA

FORMULA     : ATOM | '(' FORMULA ')' | UOP FORMULA | FORMULA BOP FORMULA 
UOP      : '!' 
BOP      : '&&' | '||' | '->' | '<->'
```
with precedence (from high to low):
```
    {!} > {&&} > {||} > {-> (ra)} > {<-> (ra)} 
```

The winning condition is defined via the locations' colors, which are natural numbers. For Safety, Reachability, Buechi, and CoBuechi a location is respectively safe, target, Buechi accepting, coBuechi accepting (should be visited eventually always) if and only if the number is greater than zero. For ParitMaxOdd the number is the color in the parity game.

An Issy specification can contain multiple logical and game specifications, which are interpreted conjunctively. 
At most one of them is allowed to be a non-safety game, respectively not a syntactic safety RPLTL formula.

## Atomic Predicates

```
ATOM    : APRED | BCONST | IDENTIFIER['''] | 'havoc' '('IDENTIFIER* ')' | 'keep' '(' IDENTIFIER* ')'
BCONST  : 'true'  | 'false'
APRED   : '[' PRED ']'
PRED    : CONST | IDENTIFIER['''] | '(' PRED ')' | AUOP PRED | PRED ABOP PRED
CONST   : NAT   | RAT
AUOP    : '*' | '+' | '-' | '/' | 'mod' | '=' | '<' | '>'| '<=' | '>='
ABOP    : '-' | 'abs'
```
with precedence (from high to low):
```
    {abs} > {*, /, mod} > {+, -} > {<, >, =, <=, >=}
```

### Macros

Macros make writing specifications more convenient, as illustrated in the simple [example](./sample.issy).

```
MACRO   : 'def' IDENTIFIER '=' FORMULA | APRED
```
Note macros can be used in all RPLTL, FORMULA, and PRED. However, for usage in PRED the marco term has to be a single predicate term!

### Identifiers and Numerical Constants
```
IDENTIFIER      : ALPHA (ALPHA | DIGIT | '_')*
NAT             : DIGIT+
RAT             : DIGIT+ '.' DIGIT+
```

### Comments
- single line '/ /'
- multi-line / * , comments are not nested!
