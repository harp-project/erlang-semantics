f(X,Y) -> X + Y.

main() ->
  case {2,3} of
    {2,1} -> nok;
    {2,3} -> f(2,3)
  end == 5.

