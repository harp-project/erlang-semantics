f(X) -> X * 2.

main() ->
  begin 
    Fun = fun ({X,1}) -> f(X) + 1; 
              ({X,Y}) -> X + Y
          end,
    Fun({1,1}) + Fun({1,2})
  end == 6.
