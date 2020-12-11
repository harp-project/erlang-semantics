map(F, []) -> [];
map(F, [H | T]) -> [F(H) | map(F,T)].

main() ->
  begin
    Fun = fun (X) -> X + 1 end,
    List = [1,2,3],
    map(Fun, List)
  end == [2,3,4].
