sum1(X) ->
  sum1_(X,0).

sum1_(X,S) ->
  case X /= 0 of
    true -> sum1_(X-1, S+X);
    false -> S
  end.

sum2(X) -> (X*(X+1)) div 2.

main() -> sum1(5) == sum2(5).      
