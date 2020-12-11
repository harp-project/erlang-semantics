main() ->
  case {1,1} of
    {A,B} when A < B -> A;
    {A,B} when A > B -> B
  end.

