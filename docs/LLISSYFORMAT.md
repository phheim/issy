# Low-Level Format for Reactive Synthesis of Infinite-State Systems 

This document descibes the Low-Level Format for Reactive Synthesis of Infinite-State Systems (LLISSY). This document is still somewhat preliminary and might change upon discussion with the academic community.

The of the LLISSYS goals include:
- Having a common format for the reactive synthesis of initite-state systems.
- The format should be able to cover benchmarks from both existing game and formula based approaches.
- The format a stable such that tools can be used and compared to long in the future.
- The format should be easy to parse without external libraries to lift burden on the tool devlopers.
- The format should still be human-readable to some extend.

The LLISSYS non-goals are:
- The format should not be necissarily easy to write for humans.
- The format should not include syntactic sugar.
- The format should no try to avoid syntactic clutter.

In order form humans to use it the benchmarks should be writte in a higher-level format, which is more adapted to humans, has syntactic sugar and might develope faster over time and is then compiled down to the LLISSY. A common usage chain should therefore be
```
    Specifier -> High-level format -> Compiler -> LLISSY -> Synthesis tool -> Result
```

## Formalism

As a formulism we use RP-LTL and the symbolic games from the paper TODO: CITE as those covers other formalism as TSL-MT (TODO: CITE), ....

## Grammar

In order to be easy to parse and still be readable and to be similiar to the SMTLib-format, the LLISSYS uses s-expression.

Only sinlge line comments exist which start with ';' to the end of the line. Newlines are be '\r\n', '\n\r', '\r' and '\n'. However, when generating LLISSY automatically '\n' should be used. Similarly ' ' (Space) and '\t' (Tabs) are both non-newline whitespace. However, only ' ' should be used upon generation. Following notions define identifiers and natural numbers.
```
ALPHA : 'a'...'z' | 'A'...'Z'
DIGIT : '0'...'9'
ID    : ALPHA (ALPHA | DIGIT | '_')*
PID   : ID ['~']
NAT   : DIGIT+
RAT   : DIGIT+ '.' DIGIT+
```
Note that all of these should be parse greedily until a whitespace, '(', ')', or the end-of-file occurs.

A specification consits of lists of variable declarations, formula specifications and game specifications. The variables declare all variables usable in all games and formulas. The formula and game specifications are interpreted conjunctivley. However, at most one game or formula cane be a non-safety game or non-safety formula.
```
SPEC : '(' '(' VARDEC* ')' '(' FSPEC* ')' '(' GSPEC*  ')' ')'
```

A variable declaration declares an input or state variable and its respective type
```
VARDEC  : '(' 'input' ID ')' | '(' 'state' ID ')'
TYPE    : 'Int' | 'Bool' | 'Real'
``` 

A formula specification is a pair of assumption and guarantee list. Each element is an RP-LTL formula.
The assumption come first and both lists are interpreted as a conjunction 
```
FSPEC   : '(' '(' FORMULA* ')' '(' FORMULA* ')' ')'
FORMULA : '(' 'ap' TERM ')' | '(' UOP FORMULA ')' | '(' BOP FORMULA FORMULA ')' | (NOP FORMULA*)
UOP     : 'X' | 'F' | 'G' | 'not'
BOP     : 'U' | 'W' | 'R'
NOP     : 'and' | 'or'
```

A game specification constist of a list of location defintions, transition definitions from on to another locations and an objective definition.
The objetcive defined the initial locations and the winning condition. Each location is annotated with a natural number. For Safety, Reachability, Buechi, and CoBuechi a locations is safe, target, infiniteley-visitable, at-some-point-only visistable, iff the number is greater zero. For ParitMaxOdd the number is the color in the parity game.
```
GSPEC    : '(' '(' LOCDEF* ')' '(' TRANSDEF* ')' OBJ ')'
LOCDEF   : '(' ID NAT TERM ')'
TRANSDEF : '(' ID ID TERM ')'
OBJ      : '(' ID ('Safety' | 'Reachability '| 'Buechi' | 'CoBuechi' | 'ParityMaxOdd') ')'
```

A term is basically like in the SMT-Lib-2 format without quantifiers, lambda, and let expressions. Similar rules for typing apply (TODO make more precise). 
Only variables declared initially are allowed to be free variables, and additionally primed version (with ~) of the state variables.
```
TERM   : '(' OP TERM* ')' | PID | CONSTS
OP     : 'and ' | 'or' | 'not' | 'ite' | 'distinct' | '=>' |
         '=' | '<' | '>'| '<=' | '>=' |
         '+' | '-' | '*' | '/' | 'mod' | 'abs' | 'to_real' 
CONSTS : RAT | NAT | 'true' | 'false'
```
