main() ->
  fun Fact (1) -> 1;
    Fact (X) -> X * Fact (X - 1)
  end(5) == 120.
