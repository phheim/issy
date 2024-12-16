# Issy Format

This document describes the high-level format used by the Issy tool.

## Syntax
```
SPEC     : (VARDECL | GAMEDEF | LOGICDEF | MACRO)*
```

### Variables
```
VARDECL  : ('input' | 'state') TYPE ID
TYPE     : 'int' | 'bool' | 'real'
```

### Formula Specifications
```
LOGICDEF : 'formula' '{' LOGICSTM*  '}'
LOGICSTM : ('assert' | 'assume') RPLTL
RPLTL    :  GPRED | CONST | ID['''] | '(' RPLTL ')' | UOP RPLTL | RPLTL BOP RPLTL 
CONST    : 'true' | 'false'
UOP      : '!' | 'F' | 'X' | 'G'
BOP      : '&&' | '||' | '->' | '<->' | 'U' | 'W' | 'R'
```
with precedence as TLSF.


### Game Specifications
```
GAMEDEF  : 'game' WINCOND 'from' ID '{' ( LOCDEF | TRANSDEF)* '}' 
WINCOND  : 'Safety' | 'Reachability' | 'Buechi' | 'CoBuechi' | 'ParityMaxOdd' 
LOCDEF   : 'loc' ID [NAT] ['with' TERM]
TRANSDEF : 'from' ID 'to' ID 'with' TERM

TERM     : GPRED | CONST | ID['''] | '(' TERM ')' | UOP TERM | TERM BOP TERM 
CONST    : 'true'  | 'false'
UOP      : '!' 
BOP      : '&&' | '||' | '->' | '<->'
```
with precedence (from high to low):
```
    {!} > {&&} > {||} > {-> (ra)} > {<-> (ra)} 
```

## Ground Predicates

```
GPRED   : '[' GROUND ']'
GROUND  : CONST | ID['''] | '(' GROUND ')' | GUOP GROUND | GROUND GBOP GROUND
CONST   : NAT   | RAT
GUOP    : '*' | '+' | '-' | '/' | 'mod' | '=' | '<' | '>'| '<=' | '>='
GBOP    : '-' | 'abs'
```
with precedence (from high to low):
```
    {abs} > {*, /, mod} > {+, -} > {<, >, =, <=, >=}
```

### Macros

```
MACRO   : 'def' ID '=' TERM
```
Note macros can be used in all RPLTL, TERM, and GROUND. However, for usage in GROUND the marco term has to be a single ground predicate term!

### Basics
```
ID      : ALPHA (ALPHA | DIGIT | '_')*
NAT     : DIGIT+
RAT     : DIGIT+ '.' DIGIT+
```

### Comments
- single line '/ /'
- multi-line / * , comments are not nested!
