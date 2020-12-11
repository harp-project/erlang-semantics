main() ->
 begin
    Foo = 1,
    fun F (1) -> 1;
        F (X) ->
          begin
            Y = X,
            FunG = fun G (1) -> 1; G (X) -> begin W = X, G(W - Foo) end end,
            F(Y - Foo) * Foo * FunG(2)
          end
    end(3)
  end == 1.
