f(X) -> X * 2.

main() ->
  begin
    Z = 2,
    Fun = fun ({X,1}) -> X * 2 + 1; 
              ({X,Y}) -> begin Z2 = Z, fun(X,Y) -> X + Y + Z2 end(X,Y) end 
          end,
    Fun({1,1}) + Fun({1,f(1)})
  end == 8.
