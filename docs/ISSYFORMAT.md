# Issy Format

This document describes the high-level format used by the Issy tool.

```
SPEC     : (VARDECL | GAMEDEF | LOGICDEF | MACRO)*

VARDECL  : ('input' | 'state') TYPE VID

LOGICDEF : 'logic' '{' LOGICSTM*  '}'
LOGICSTM : ('assert' | 'assume') RPLTL
RPLTL    : '(' RPLTL ')' | UOP RPLTL RPLTL | RPLTL BOP RPLTL | FOL
UOP      : '!' | 'F' | 'X' | 'G'
BOP      : '&&' | '||' | 'U' | 'W' | 'R' | '->'

Precdence 
        as TLSF!

GAMEDEF  : 'game' WINCOND 'from' LID '{' ( LOCDEF | TRANSDEF)* '}' 
WINCOND  : 'Safety' | 'Reachability' | 'Buechi' | 'CoBuechi' | 'ParityMaxOdd' 
LOCDEF   : 'loc' LID [NAT] [FOL]
TRANSDEF : 'from' LID 'to' LID 'with' FOL

FOL      : '[' TERM ']'
TERM     : CONST | VID | VID''' | '(' TERM ')' | UOP TERM | TERM BOP TERM | 'ite' TERM TERM TERM
CONST    : NAT | RAT | 'true' | 'false'
UOP      : '!' | 'abs' | '-'
BOP      : '&&' | '||' | '*' | '+' | '-' | '/' | 'mod' | '->' | '<->'

Precedence :
        ite, <->, ->, ||, &&, '!', 'mod', '*', '/', '+', '-', 'abs'
```
