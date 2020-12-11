f(X) -> X + 1.

main() ->
  case {3,2} of
    {A,B} when A < B -> f(A);
    {A,B} when A > B -> f(B);
    {A,B} when A == B -> equal
  end == 3.

