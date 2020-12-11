main() ->
  begin
    Fact = 1,
    fun Fact (1) -> 1;
        Fact (X) -> begin Fun = Fact, X  * Fun(X - 1) end
    end(5) + Fact == 121
  end.
