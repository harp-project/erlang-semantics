# KErl: Executable semantics for Erlang

Executable formal semantics for a subset of the Erlang programming language defined in the K Framework. This definition works with K version 3.6, but may be incompatible with more recent releases of K.

The first version of this formalization was implemented by Judit Kőszegi in 2015 (see http://ceur-ws.org/Vol-2046/koszegi.pdf for details).
Formal proof sketches described in https://arxiv.org/pdf/1708.07225.pdf are built upon this formalization of Erlang.

## Features implemented

- Literals: integer, atom, tuple, list
- Variables and variable environments
- Arithmetic, logic and comparison operators (not complete)
- Basic operations on lists, list comprehension
- Function call (intra- and intermodule)
- Basic built-in functions
- Case expression (without guards)
- If expression
- Match expression
- Expression sequences within begin-end
- Fun expression
- Top-level function defenition (without guards)
- Module structure, attributes

## Future work

- Maps
- Bit syntax
- Exception handling
- Basic IO
- Concurrency
