sum([]) -> 0;
sum([H | T]) -> H + sum(T).

main() -> 15 == sum([1,2,3,4,5]).
