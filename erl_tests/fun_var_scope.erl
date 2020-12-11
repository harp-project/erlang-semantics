main() ->
  begin
    X = 1,
    Fun =
      fun
        ({X,Y}) -> X + Y; 
        ({Y})   -> X + Y
      end,
    Fun({2,3}) == 5 andalso Fun({3}) == 4
  end.
