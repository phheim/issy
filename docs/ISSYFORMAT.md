# Issy Format

This document describes the high-level format used by the Issy tool.

## Syntax
```
SPEC     : (VARDECL | LOGICSPEC | GAMESPEC | MACRO)*
```

### Variable Declarations
```
VARDECL  : ('input' | 'state') TYPE IDENTIFIER
TYPE     : 'int' | 'bool' | 'real'
```

### Formula Specifications
```
LOGICSPEC : 'formula' '{' LOGICSTM*  '}'
LOGICSTM  : ('assert' | 'assume') RPLTL
RPLTL     : ATOM | '(' RPLTL ')' | UOPT RPLTL | RPLTL BOPT RPLTL 
UOPT      : '!' | 'F' | 'X' | 'G'
BOPT      : '&&' | '||' | '->' | '<->' | 'U' | 'W' | 'R'
```
with precedence as TLSF.


### Game Specifications
```
GAMESPEC  : 'game' WINCOND 'from' IDENTIFIER '{' ( LOCDEF | TRANSDEF)* '}' 
WINCOND   : 'Safety' | 'Reachability' | 'Buechi' | 'CoBuechi' | 'ParityMaxOdd' 
LOCDEF    : 'loc' IDENTIFIER [NAT] ['with' TERM]
TRANSDEF  : 'from' IDENTIFIER 'to' IDENTIFIER 'with' TERM

TERM     : ATOM | '(' TERM ')' | UOP TERM | TERM BOP TERM 
UOP      : '!' 
BOP      : '&&' | '||' | '->' | '<->'
```
with precedence (from high to low):
```
    {!} > {&&} > {||} > {-> (ra)} > {<-> (ra)} 
```

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
MACRO   : 'def' IDENTIFIER '=' TERM
```
Note macros can be used in all RPLTL, TERM, and PRED. However, for usage in PRED the marco term has to be a single predicate term!

### Identifiers and Numerical Constants
```
IDENTIFIER      : ALPHA (ALPHA | DIGIT | '_')*
NAT             : DIGIT+
RAT             : DIGIT+ '.' DIGIT+
```

### Comments
- single line '/ /'
- multi-line / * , comments are not nested!
