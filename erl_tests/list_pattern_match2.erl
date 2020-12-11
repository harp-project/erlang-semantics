main() ->
  case [1,2,3,4] of
    [X, Y | Z] -> X + Y
  end == 3.
