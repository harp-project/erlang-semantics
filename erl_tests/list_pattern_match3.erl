main() ->
  case [1,2,3,4,5] of
    [X, Y | [_,Z | W]] -> X + Y + Z + hd(W)
  end == 12.
