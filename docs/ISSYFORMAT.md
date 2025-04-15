# Issy Format

This document describes the high-level format used by the Issy tool. A simple example can be found [here](./docs/sample.issy).

## Syntax
An Issy specification consists of variable declarations, formula specifications, game specifications and macro definitions for better readability.

```
SPEC     : (VARDECL | LOGICSPEC | GAMESPEC | MACRO)*
```

### Variable Declarations

Variable declarations specify whether the variable is input controlled by the environment, or is a state variable controlled by the system. The currently supported data types are bool, int and real.

```
VARDECL  : ('input' | 'state') TYPE IDENTIFIER
TYPE     : 'int' | 'bool' | 'real'
```

### Formula Specifications

The formula specification is a list of RPLTL formulas, prefixed by the keywords 'assume' and 'assert', denoting constraints on the environment and the system respectively. They use temporal ('X', 'F', 'G') operators like LTL, but with quantifier-free first-order atoms  instead of Boolean propositions. The precedence is like in TLSF.

```
LOGICSPEC : 'formula' '{' LOGICSTM*  '}'
LOGICSTM  : ('assert' | 'assume') RPLTL
RPLTL     : ATOM | '(' RPLTL ')' | UOPT RPLTL | RPLTL BOPT RPLTL 
UOPT      : '!' | 'F' | 'X' | 'G'
BOPT      : '&&' | '||' | '->' | '<->' | 'U' | 'W' | 'R'
```


### Game Specifications

A game specification defines the type of winning condition and the initial location of the game. Locations (which can be thought of as the values of a local program counter) have names, colors (used in the winning condition) and domain terms (which constrain the possible values of the variables). Transition defintions define the transitions between locations. They are labelled by formulas, which specify under what conditions a transition can be taken and its effect. 

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

The wiining condition is defined via the location's colors, which are natural numbers. For Safety, Reachability, Buechi, and CoBuechi a locations is safe, target, Buechi accepting, coBuechi accepting (should be visited eventually always), iff the number is greater than zero. For ParitMaxOdd the number is the color in the parity game.

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
