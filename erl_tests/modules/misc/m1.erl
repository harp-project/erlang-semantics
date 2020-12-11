-module(m1).

-export([f/1, f/2]).

f(X) -> f(X * 2, X).

f(X,Y) -> begin Foo = m2:g(X) * Y,
                Foo + 1
          end.
