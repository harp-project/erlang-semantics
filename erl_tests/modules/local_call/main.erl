-module(main).

-export([main/0, foo/1]).

main() -> foo(10) + bar(20) == 33.

foo(X) -> X + 1.
bar(X) -> X + 2.
