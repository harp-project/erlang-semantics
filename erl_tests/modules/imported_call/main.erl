-module(main).

-export([main/0]).

-import(m1,[f/1,f/2]).

-export([bar/0]).

main() -> f(1) == 3.
