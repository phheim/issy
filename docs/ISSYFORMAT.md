# Issy Format

This document describes the high-level format used by the Issy tool.

```
SPEC     : (VARDECL | GAMEDEF | LOGICDEF | MACRO)*

VARDECL  : ('input' | 'state') TYPE VID

LOGICDEF : 'logic' '{' LOGICSTM*  '}'
LOGICSTM : ('assert' | 'assume') RPLTL
RPLTL    : '(' RPLTL ')' | UOP RPLTL RPLTL | RPLTL BOP RPLTL | FOL | 'true' | 'false'
UOP      : '!' | 'F' | 'X' | 'G'
BOP      : '&&' | '||' | 'U' | 'W' | 'R' | '->' | '<->'

Precdence 
        as TLSF!

GAMEDEF  : 'game' WINCOND 'from' ID '{' ( LOCDEF | TRANSDEF)* '}' 
WINCOND  : 'Safety' | 'Reachability' | 'Buechi' | 'CoBuechi' | 'ParityMaxOdd' 
LOCDEF   : 'loc' ID [NAT] [FOL]
TRANSDEF : 'from' ID 'to' ID 'with' FOL

FOL      : '[' TERM ']'
TERM     : CONST | ID['''] | '(' TERM ')' | UOP TERM | TERM BOP TERM
CONST    : NAT | RAT | 'true' | 'false'
UOP      : '!' | 'abs' | '-'
BOP      : '&&' | '||' | '*' | '+' | '-' | '/' | 'mod' | '->' | '<->' | '=' | '<' | '>'| '<=' | '>='

Precedence (low to high):
        <->, ->, ||, &&, '!', '<', '>', '=', '<=', '>=' , 'mod', '/', '*', '+', '-', 'abs'

MACRO   : 'def' ID '=' FOL 

ID      : ALPHA (ALPHA | DIGIT | '_')*
NAT     : DIGIT+
RAT     : DIGIT+ '.' DIGIT+
```

Comments
- single line '/ /'
- multi-line / * , comments are not nested!
