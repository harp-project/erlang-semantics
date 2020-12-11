main() ->
  case {2,3} of
    {A,B} when A < B -> A;
    {A,B} when A > B -> B;
    {A,B} when A == B -> equal
  end == 2.

