main() ->
  begin
    X = 1,
    [X || X > 1, X <- [1,2,3]] == []
  end.
