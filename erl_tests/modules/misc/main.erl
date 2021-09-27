-module(main).

-export([main/0, foo/1]).

-import(m1,[f/1,f/2]).

-export([bar/0]).

main() -> foo(1) + f(1) + m1:f(2) == 23 .

foo(X) -> X.
bar() -> ok.
